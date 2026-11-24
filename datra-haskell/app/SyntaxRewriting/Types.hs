module SyntaxRewriting.Types
  ( SyntaxType (..)
  , SyntaxContext (..)
  , SyntaxRuleFamily (..)
  , ClassifyHoles
  , CaptureHole
  , RewriteRule (..)
  , CaptureExtent (..)
  , RewriteNodeId (..)
  , RewriteLocus (..)
  , StructuralCandidate (..)
  , SelectedCandidate (..)
  , PreparedExpansion (..)
  , CandidateTypingContext (..)
  , Compatibility (..)
  , CompatibilityConstraint (..)
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
import StringExpression
  ( TemplateSelection )
import DatraTypes
  ( InterpretedValue
  , SyntaxFunctionExpansion
  , SyntaxFunctionInsertion
  )
import StringInterpolation
  ( DeclarativeCapture
  , SyntaxRule
  )

data SyntaxType = SyntaxType
  { syntaxTypeExpression :: Expression
  , syntaxTypeRuntimeValue :: Maybe InterpretedValue
  }

type ClassifyHoles syntaxType =
  [DeclarativeCapture]
  -> [(DeclarativeCapture, Maybe syntaxType)]

type CaptureHole =
  [(DeclarativeCapture, Expression)]
  -> DeclarativeCapture
  -> Expression
  -> Maybe Expression

data SyntaxRuleFamily syntaxType = SyntaxRuleFamily
  { syntaxRuleFamilyNames :: [String]
  , syntaxRuleFamilyRules :: [(Int, SyntaxRule)]
  , syntaxRuleFamilyEvaluate :: Expression -> Maybe syntaxType
  }

data SyntaxContext syntaxType = SyntaxContext
  { contextSourceSpan :: Maybe SourceSpan
  , contextRuleFamilies :: [SyntaxRuleFamily syntaxType]
  , contextClassify :: ClassifyHoles syntaxType
  , contextCapture :: CaptureHole
  , contextResultType :: Expression -> Maybe syntaxType
  , contextSyntaxInsertion
      :: Expression
      -> Maybe SyntaxFunctionInsertion
  , contextAssembleImplicitResource
      :: [Expression]
      -> Either SyntaxRewriteFailure Expression
  , contextExpandSyntax
      :: SyntaxFunctionExpansion
      -> Either SyntaxRewriteFailure Expression
  , contextRewriteScope :: RewriteLocus -> SyntaxContext syntaxType
  , contextPublish :: Expression -> Maybe (SyntaxContext syntaxType)
  , contextRecursive :: [Expression] -> SyntaxContext syntaxType
  , contextScope :: Expression -> SyntaxContext syntaxType
  , contextEnter :: Maybe Expression -> SyntaxContext syntaxType
  }

data RewriteRule syntaxType = RewriteRule
  { rewriteRule :: SyntaxRule
  , rewriteRuleBranch :: Int
  , rewriteRuleSyntaxInsertion :: Maybe SyntaxFunctionInsertion
  , rewriteRuleReturnType :: Maybe syntaxType
  }

data CaptureExtent
  = WholeCaptureExtent
  | ProperCaptureExtent
  deriving (Eq, Show)

newtype RewriteNodeId = RewriteNodeId Int
  deriving (Eq, Ord, Show)

-- | The only scope question the rewrite machine asks the interpreter.  A
-- detached expression is a root, capture, or freshly expanded expression;
-- a child locus additionally describes the semantic edge used to reach it.
data RewriteLocus
  = RewriteExpression Expression
  | RewriteChild Expression Int Expression

data StructuralCandidate syntaxType = StructuralCandidate
  { structuralCandidateRule :: RewriteRule syntaxType
  , structuralCandidateSelection
      :: TemplateSelection Expression Expression
  , structuralCandidateCaptures
      :: [(DeclarativeCapture, Expression, CaptureExtent)]
  , structuralCandidateRemaining :: [Expression]
  }

data SelectedCandidate syntaxType = SelectedCandidate
  { selectedStructuralCandidate :: StructuralCandidate syntaxType
  , selectedCaptures :: [RewriteResult syntaxType]
  , selectedReturnType :: syntaxType
  , selectedTypingContext :: CandidateTypingContext syntaxType
  }

data PreparedExpansion = PreparedExpansion
  { preparedExpansionSyntax :: SyntaxFunctionExpansion
  , preparedExpansionRemaining :: [Expression]
  }

data CandidateTypingContext syntaxType = CandidateTypingContext
  { candidateTypingInputs :: Map Int syntaxType
  , candidateTypingExpectedHoles :: Map Int syntaxType
  , candidateTypingDeferred
      :: [CompatibilityConstraint syntaxType]
  }

data Compatibility
  = CompatibilityProved
  | CompatibilityRefuted
  | CompatibilityDeferred
  deriving (Eq, Show)

data CompatibilityConstraint syntaxType = CompatibilityConstraint
  { compatibilitySource :: syntaxType
  , compatibilityTarget :: syntaxType
  }

data CandidateFrame syntaxType = CandidateFrame
  { candidateFrameNextCapture :: Int
  , candidateFrameTypingContext :: CandidateTypingContext syntaxType
  , candidateFrameResults :: Map Int (RewriteResult syntaxType)
  , candidateFramePreparedCaptures :: Map Int Expression
  }

data CandidateFrameProgress syntaxType
  = CandidateFrameNeedsChild
      (CandidateFrame syntaxType)
      Int
      DeclarativeCapture
      Expression
  | CandidateFrameRejected (CandidateRejectionDetails syntaxType)
  | CandidateFrameAccepted
      (CandidateTypingContext syntaxType)
      [RewriteResult syntaxType]
      syntaxType

data CandidateRejectionDetails syntaxType = CandidateRejectionDetails
  { candidateRejectionRule :: RewriteRule syntaxType
  , candidateRejectionBranch :: Int
  , candidateRejectionCaptureIndex :: Int
  , candidateRejectionSource :: Expression
  , candidateRejectionExpected :: Maybe syntaxType
  , candidateRejectionActual :: Maybe syntaxType
  , candidateRejectionContext :: CandidateTypingContext syntaxType
  , candidateRejectionReason :: CandidateRejectionReason
  }

data CandidateRejection syntaxType = CandidateRejection
  { candidateRejectionDiagnostic
      :: DatraError (CandidateRejectionDetails syntaxType)
  , candidateRejectionChildren :: [CandidateRejection syntaxType]
  }

data RewriteResult syntaxType = RewriteResult
  { rewriteResultExpression :: Expression
  , rewriteResultType :: Maybe syntaxType
  , rewriteResultSelection :: Maybe (SelectedCandidate syntaxType)
  , rewriteResultDeferred
      :: [CompatibilityConstraint syntaxType]
  }

data CandidateSearch syntaxType = CandidateSearch
  { candidateSearchCandidates :: [StructuralCandidate syntaxType]
  , candidateSearchCursor :: Int
  , candidateSearchRejections :: [CandidateRejection syntaxType]
  , candidateSearchFrame :: Maybe (CandidateFrame syntaxType)
  }

data OrdinaryTraversal syntaxType = OrdinaryTraversal
  { ordinaryTraversalCursor :: Int
  , ordinaryTraversalSelection :: Maybe (SelectedCandidate syntaxType)
  , ordinaryTraversalFinalizedCaptures :: [Expression]
  , ordinaryTraversalDeferred
      :: [CompatibilityConstraint syntaxType]
  }

data RewriteWork syntaxType
  = SearchCandidates (CandidateSearch syntaxType)
  | TraverseChildren (OrdinaryTraversal syntaxType)

data RewriteNodeState syntaxType
  = NodePending
  | NodeReady (RewriteWork syntaxType)
  | NodeWaiting (RewriteWork syntaxType) RewriteNodeId
  | NodeFinalized (RewriteResult syntaxType)

data RewriteNode environment syntaxType = RewriteNode
  { rewriteNodeExpression :: Expression
  , rewriteNodeEnvironment :: environment
  , rewriteNodeParent :: Maybe RewriteNodeId
  , rewriteNodeRejections :: [CandidateRejection syntaxType]
  , rewriteNodeState :: RewriteNodeState syntaxType
  }
