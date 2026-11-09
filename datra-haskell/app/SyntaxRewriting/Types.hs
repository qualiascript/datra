module SyntaxRewriting.Types
  ( SyntaxContext (..)
  , SyntaxRuleFamily (..)
  , ClassifyHoles
  , CaptureHole
  , RewriteRule (..)
  , RewriteNodeId (..)
  , RewriteLocus (..)
  , StructuralCandidate (..)
  , SelectedCandidate (..)
  , PreparedExpansion (..)
  , CandidateTypingContext (..)
  , CandidateFrame (..)
  , CandidateFrameProgress (..)
  , CandidateRejectionReason (..)
  , CandidateRejectionDetails (..)
  , CandidateRejection (..)
  , RewriteResult (..)
  , CandidateSearch (..)
  , OrdinaryTraversal (..)
  , RewriteWork (..)
  , RewriteNodeState (..)
  , RewriteNode (..)
  ) where

import Data.Map.Strict (Map)
import DatraLanguage.AST (Expression)
import DatraLanguage.Diagnostics (DatraError, SourceSpan)
import DatraLanguage.Diagnostics.Application
  ( CandidateRejectionReason (..), SyntaxRewriteFailure )
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind
  , TemplateSelection
  )
import DatraTypes
  ( InterpretedValue
  , SyntaxFunctionExpansion
  , SyntaxFunctionInsertion
  )
import SyntaxDefinitions (SyntaxRule)

type ClassifyHoles =
  [SyntaxHoleKind Expression]
  -> [(SyntaxHoleKind Expression, Maybe InterpretedValue)]

type CaptureHole =
  [(SyntaxHoleKind Expression, Expression)]
  -> SyntaxHoleKind Expression
  -> Expression
  -> Maybe Expression

data SyntaxRuleFamily = SyntaxRuleFamily
  { syntaxRuleFamilyNames :: [String]
  , syntaxRuleFamilyRules :: [(Int, SyntaxRule)]
  , syntaxRuleFamilyClassify :: ClassifyHoles
  , syntaxRuleFamilyEvaluate :: Expression -> Maybe InterpretedValue
  , syntaxRuleFamilyApply
      :: Expression
      -> InterpretedValue
      -> Maybe InterpretedValue
  }

data SyntaxContext = SyntaxContext
  { contextSourceSpan :: Maybe SourceSpan
  , contextRuleFamilies :: [SyntaxRuleFamily]
  , contextClassify :: ClassifyHoles
  , contextCapture :: CaptureHole
  , contextEvaluate :: Expression -> Maybe InterpretedValue
  , contextResultType :: Expression -> Maybe InterpretedValue
  , contextEvaluateWithInput
      :: InterpretedValue
      -> Expression
      -> Maybe InterpretedValue
  , contextApply
      :: Expression
      -> InterpretedValue
      -> Maybe InterpretedValue
  , contextAssembleImplicitResource
      :: [Expression]
      -> Either SyntaxRewriteFailure Expression
  , contextExpandSyntax
      :: SyntaxFunctionExpansion
      -> Either SyntaxRewriteFailure Expression
  , contextRewriteScope :: RewriteLocus -> SyntaxContext
  , contextPublish :: Expression -> Maybe SyntaxContext
  , contextRecursive :: [Expression] -> SyntaxContext
  , contextScope :: Expression -> SyntaxContext
  , contextEnter :: Maybe Expression -> SyntaxContext
  }

data RewriteRule = RewriteRule
  { rewriteRule :: SyntaxRule
  , rewriteRuleBranch :: Int
  , rewriteRuleEvaluation :: Maybe (Expression -> Maybe InterpretedValue)
  , rewriteRuleHoleFamilies :: [Maybe InterpretedValue]
  , rewriteRuleSyntaxInsertion :: Maybe SyntaxFunctionInsertion
  , rewriteRuleReturnType :: Maybe InterpretedValue
  }

newtype RewriteNodeId = RewriteNodeId Int
  deriving (Eq, Ord, Show)

-- | The only scope question the rewrite machine asks the interpreter.  A
-- detached expression is a root, capture, or freshly expanded expression;
-- a child locus additionally describes the semantic edge used to reach it.
data RewriteLocus
  = RewriteExpression Expression
  | RewriteChild Expression Int Expression

data StructuralCandidate = StructuralCandidate
  { structuralCandidateRule :: RewriteRule
  , structuralCandidateBranch :: Int
  , structuralCandidateProjection :: Int
  , structuralCandidateSelection
      :: TemplateSelection Expression Expression
  , structuralCandidateCaptures
      :: [(SyntaxHoleKind Expression, Expression)]
  , structuralCandidateRemaining :: [Expression]
  }

data SelectedCandidate = SelectedCandidate
  { selectedStructuralCandidate :: StructuralCandidate
  , selectedCaptures :: [RewriteResult]
  , selectedReturnType :: InterpretedValue
  }

data PreparedExpansion = PreparedExpansion
  { preparedExpansionSyntax :: SyntaxFunctionExpansion
  , preparedExpansionRemaining :: [Expression]
  }

data CandidateTypingContext = CandidateTypingContext
  { candidateTypingInputs :: Map Int InterpretedValue
  , candidateTypingExpectedHoles :: Map Int InterpretedValue
  , candidateTypingReturnType :: Maybe InterpretedValue
  }

data CandidateFrame = CandidateFrame
  { candidateFrameNextCapture :: Int
  , candidateFrameTypingContext :: CandidateTypingContext
  , candidateFrameResults :: Map Int RewriteResult
  , candidateFramePreparedCaptures :: Map Int Expression
  }

data CandidateFrameProgress
  = CandidateFrameNeedsChild
      CandidateFrame
      Int
      (SyntaxHoleKind Expression)
      Expression
  | CandidateFrameRejected CandidateRejectionDetails
  | CandidateFrameAccepted
      CandidateTypingContext
      [RewriteResult]
      InterpretedValue

data CandidateRejectionDetails = CandidateRejectionDetails
  { candidateRejectionRule :: RewriteRule
  , candidateRejectionBranch :: Int
  , candidateRejectionCaptureIndex :: Int
  , candidateRejectionSource :: Expression
  , candidateRejectionExpected :: Maybe InterpretedValue
  , candidateRejectionActual :: Maybe InterpretedValue
  , candidateRejectionContext :: CandidateTypingContext
  , candidateRejectionReason :: CandidateRejectionReason
  }

data CandidateRejection = CandidateRejection
  { candidateRejectionDiagnostic
      :: DatraError CandidateRejectionDetails
  , candidateRejectionChildren :: [CandidateRejection]
  }

data RewriteResult = RewriteResult
  { rewriteResultExpression :: Expression
  , rewriteResultType :: Maybe InterpretedValue
  , rewriteResultSelection :: Maybe SelectedCandidate
  }

data CandidateSearch = CandidateSearch
  { candidateSearchCandidates :: [StructuralCandidate]
  , candidateSearchCursor :: Int
  , candidateSearchRejections :: [CandidateRejection]
  , candidateSearchFrame :: Maybe CandidateFrame
  }

data OrdinaryTraversal = OrdinaryTraversal
  { ordinaryTraversalCursor :: Int
  , ordinaryTraversalSelection :: Maybe SelectedCandidate
  , ordinaryTraversalFinalizedCaptures :: [Expression]
  }

data RewriteWork
  = SearchCandidates CandidateSearch
  | TraverseChildren OrdinaryTraversal

data RewriteNodeState
  = NodePending
  | NodeReady RewriteWork
  | NodeWaiting RewriteWork RewriteNodeId
  | NodeFinalized RewriteResult

data RewriteNode environment = RewriteNode
  { rewriteNodeExpression :: Expression
  , rewriteNodeEnvironment :: environment
  , rewriteNodeParent :: Maybe RewriteNodeId
  , rewriteNodeRejections :: [CandidateRejection]
  , rewriteNodeState :: RewriteNodeState
  }
