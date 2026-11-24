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
import Rendering (renderInterpretedValue)
import SyntaxRewriting.Types
  ( CandidateRejection (..)
  , CandidateRejectionDetails (..)
  , CandidateTypingContext (..)
  , SyntaxType (..)
  )
import Data.Map.Strict qualified as Map

candidateRejectionAt
  :: Maybe SourceSpan
  -> CandidateRejectionDetails syntaxType
  -> [CandidateRejection syntaxType]
  -> CandidateRejection syntaxType
candidateRejectionAt sourceSpan details children = CandidateRejection
  { candidateRejectionDiagnostic = maybe
      (withoutSourceSpan details)
      (`atSourceSpan` details)
      sourceSpan
  , candidateRejectionChildren = children
  }

reportCandidateRejections
  :: [CandidateRejection SyntaxType]
  -> [DatraError CandidateRejectionReport]
reportCandidateRejections = map report . flattenCandidateRejections
  where
    report rejection = fmap summarize
      (candidateRejectionDiagnostic rejection)
    summarize details = CandidateRejectionReport
      { rejectedCandidateBranch = candidateRejectionBranch details
      , rejectedCandidateCapture = candidateRejectionCaptureIndex details
      , rejectedCandidateSource = renderSourceExpression
          (candidateRejectionSource details)
      , rejectedCandidateExpected =
          renderSyntaxType <$> candidateRejectionExpected details
      , rejectedCandidateActual =
          renderSyntaxType <$> candidateRejectionActual details
      , rejectedCandidateInputs =
          [ (index, renderSyntaxType value)
          | (index, value) <- Map.toAscList
              (candidateTypingInputs (candidateRejectionContext details))
          ]
      , rejectedCandidateReason = candidateRejectionReason details
      }
    renderSyntaxType syntaxType = case syntaxTypeRuntimeValue syntaxType of
      Just runtimeValue -> renderInterpretedValue runtimeValue
      Nothing -> renderSourceExpression (syntaxTypeExpression syntaxType)

-- | Preserve semantic attempt order while exposing nested causal paths to a
-- diagnostic renderer.  Children immediately follow the parent candidate
-- whose required match exhausted.
flattenCandidateRejections
  :: [CandidateRejection syntaxType]
  -> [CandidateRejection syntaxType]
flattenCandidateRejections = concatMap flatten
  where
    flatten rejection = rejection :
      flattenCandidateRejections (candidateRejectionChildren rejection)
