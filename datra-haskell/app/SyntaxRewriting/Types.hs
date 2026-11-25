module SyntaxRewriting.Types
  ( RewriteRule (..)
  , CaptureExtent (..)
  , RewriteNodeId (..)
  , RewriteLocus (..)
  , StructuralCandidate (..)
  , SelectedCandidate (..)
  , PreparedExpansion (..)
  , CandidateDecision (..)
  , HeldCandidate (..)
  , CandidateTypingContext (..)
  , CandidateFrame (..)
  , CandidateFrameProgress (..)
  , CandidateRejectionReason (..)
  , CandidateRejectionDetails (..)
  , CandidateRejection (..)
  , RewriteResult (..)
  , ProvisionalCandidate (..)
  , CandidateSearch (..)
  , OrdinaryTraversal (..)
  , RewriteWork (..)
  , RewriteNodeState (..)
  , RewriteNode (..)
  ) where

import Data.Map.Strict (Map)
import DatraLanguage.AST (Expression)
import DatraLanguage.Diagnostics (DatraError)
import DatraLanguage.Diagnostics.Application
  ( CandidateRejectionReason (..) )
import StringExpression
  ( TemplateSelection )
import DatraTypes
  ( InterpretedValue )
import DatraTypes.Scope
  ( DeclarationLayerImportPolicy, Scope )
import StringInterpolation
  ( DeclarativeCapture
  , SyntaxRule
  )

data RewriteRule = RewriteRule
  { rewriteRule :: SyntaxRule
  , rewriteRuleBranch :: Int
  , rewriteRuleReturnType :: Maybe InterpretedValue
  , rewriteRuleFamilyScope :: Scope
  , rewriteRuleImportPolicy :: DeclarationLayerImportPolicy
  , rewriteRuleLayer :: Int
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

data StructuralCandidate = StructuralCandidate
  { structuralCandidateRule :: RewriteRule
  , structuralCandidateSelection
      :: TemplateSelection Expression Expression
  , structuralCandidateCaptures
      :: [(DeclarativeCapture, Expression, CaptureExtent)]
  , structuralCandidateRemaining :: [Expression]
  }

data SelectedCandidate = SelectedCandidate
  { selectedStructuralCandidate :: StructuralCandidate
  , selectedCaptures :: [RewriteResult]
  , selectedReturnType :: Maybe InterpretedValue
  , selectedTypingContext :: CandidateTypingContext
  }

data PreparedExpansion = PreparedExpansion
  { preparedExpansionExpression :: Expression
  , preparedExpansionRemaining :: [Expression]
  }

data CandidateDecision
  = CandidateAccepted InterpretedValue
  | CandidateHeld [Expression] CandidateRejectionDetails
  | CandidateRefuted CandidateRejectionDetails

data HeldCandidate = HeldCandidate
  { heldCandidateSearch :: CandidateSearch
  , heldCandidateSelected :: SelectedCandidate
  , heldCandidatePrepared :: PreparedExpansion
  , heldCandidateBlockers :: [Expression]
  , heldCandidateFallback :: CandidateRejectionDetails
  }

data CandidateTypingContext = CandidateTypingContext
  { candidateTypingInputs :: Map Int InterpretedValue
  , candidateTypingExpectedHoles :: Map Int InterpretedValue
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
      DeclarativeCapture
      Expression
  | CandidateFrameNeedsTerminal
      CandidateFrame
      Int
      DeclarativeCapture
      Expression
  | CandidateFrameRejected CandidateRejectionDetails
  | CandidateFrameComplete
      CandidateTypingContext
      [RewriteResult]

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

data ProvisionalCandidate = ProvisionalCandidate
  { provisionalCandidateSelected :: SelectedCandidate
  , provisionalCandidatePrepared :: PreparedExpansion
  , provisionalCandidateReturnType :: InterpretedValue
  }

data CandidateSearch = CandidateSearch
  { candidateSearchCandidates :: [StructuralCandidate]
  , candidateSearchCursor :: Int
  , candidateSearchRejections :: [CandidateRejection]
  , candidateSearchFrame :: Maybe CandidateFrame
  , candidateSearchProvisional :: Maybe ProvisionalCandidate
  }

data OrdinaryTraversal = OrdinaryTraversal
  { ordinaryTraversalCursor :: Int
  , ordinaryTraversalSelection :: Maybe SelectedCandidate
  , ordinaryTraversalFinalizedCaptures :: Map Expression Int
  , ordinaryTraversalPending :: Map Int RewriteNodeId
  }

data RewriteWork
  = SearchCandidates CandidateSearch
  | DecideCandidate HeldCandidate
  | TraverseChildren OrdinaryTraversal

data RewriteNodeState
  = NodePending
  | NodeReady RewriteWork
  | NodeWaiting RewriteWork RewriteNodeId
  | NodeHeld HeldCandidate
  | NodeFinalized RewriteResult

data RewriteNode environment = RewriteNode
  { rewriteNodeExpression :: Expression
  , rewriteNodeEnvironment :: environment
  , rewriteNodeParent :: Maybe RewriteNodeId
  , rewriteNodeRejections :: [CandidateRejection]
  , rewriteNodeState :: RewriteNodeState
  }
