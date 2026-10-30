module SyntaxRewriting.Diagnostics
  ( candidateRejectionAt
  , CandidateRejectionReport (..)
  , reportCandidateRejections
  , flattenCandidateRejections
  ) where

import DatraLanguage.Diagnostics
  ( DatraError (..)
  , SourceSpan
  , atSourceSpan
  , withoutSourceSpan
  )
import DatraLanguage.AST.Source (renderSourceExpression)
import DatraLanguage.Diagnostics.Application
  ( CandidateRejectionReport (..) )
import SyntaxDefinitions (SyntaxRule (syntaxName))
import Rendering (renderInterpretedValue)
import SyntaxRewriting.Types
  ( CandidateRejection (..)
  , CandidateRejectionDetails (..)
  , CandidateTypingContext (..)
  , RewriteRule (rewriteRule)
  )
import Data.Map.Strict qualified as Map

candidateRejectionAt
  :: Maybe SourceSpan
  -> CandidateRejectionDetails
  -> [CandidateRejection]
  -> CandidateRejection
candidateRejectionAt sourceSpan details children = CandidateRejection
  { candidateRejectionDiagnostic = maybe
      (withoutSourceSpan details)
      (`atSourceSpan` details)
      sourceSpan
  , candidateRejectionChildren = children
  }

reportCandidateRejections
  :: [CandidateRejection]
  -> [DatraError CandidateRejectionReport]
reportCandidateRejections = map report . flattenCandidateRejections
  where
    report rejection = fmap summarize
      (candidateRejectionDiagnostic rejection)
    summarize details = CandidateRejectionReport
      { rejectedCandidateRule = syntaxName
          (rewriteRule (candidateRejectionRule details))
      , rejectedCandidateBranch = candidateRejectionBranch details
      , rejectedCandidateCapture = candidateRejectionCaptureIndex details
      , rejectedCandidateSource = renderSourceExpression
          (candidateRejectionSource details)
      , rejectedCandidateExpected =
          renderInterpretedValue <$> candidateRejectionExpected details
      , rejectedCandidateActual =
          renderInterpretedValue <$> candidateRejectionActual details
      , rejectedCandidateInputs =
          [ (index, renderInterpretedValue value)
          | (index, value) <- Map.toAscList
              (candidateTypingInputs (candidateRejectionContext details))
          ]
      , rejectedCandidateReason = candidateRejectionReason details
      }

-- | Preserve semantic attempt order while exposing nested causal paths to a
-- diagnostic renderer.  Children immediately follow the parent candidate
-- whose required match exhausted.
flattenCandidateRejections
  :: [CandidateRejection]
  -> [CandidateRejection]
flattenCandidateRejections = concatMap flatten
  where
    flatten rejection = rejection :
      flattenCandidateRejections (candidateRejectionChildren rejection)
