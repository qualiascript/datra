module SyntaxRewriting.Types
  ( SyntaxContext (..)
  , SyntaxRuleFamily (..)
  , ClassifyHoles
  , CaptureHole
  , RewriteRule (..)
  , RewriteNodeId (..)
  , SequenceId (..)
  , RewriteDependency (..)
  , StructuralCandidate (..)
  , SelectedCandidate (..)
  , PreparedExpansion (..)
  , CandidateTypingContext (..)
  , CandidateFrame (..)
  , CandidateFrameProgress (..)
  , CandidateContinuation (..)
  , RewriteParent (..)
  , CandidateAttempt (..)
  , CandidateRejectionReason (..)
  , CandidateRejectionDetails (..)
  , CandidateRejection (..)
  , RewriteResult (..)
  , RewriteNodeState (..)
  , RewriteNode (..)
  , SequenceFrame (..)
  , RewriteTask (..)
  ) where

import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.Set qualified as Set
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
  Bool
  -> [(SyntaxHoleKind Expression, Expression)]
  -> SyntaxHoleKind Expression
  -> Expression
  -> Maybe Expression

-- | One visible declaration family, already paired with the lexical
-- interpreter operations captured at its declaration position. Syntax
-- rewriting orders and selects these families but does not construct or
-- interpret dependent declarations.
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
  , contextAssembleSequence
      :: Expression
      -> [Expression]
      -> Either SyntaxRewriteFailure Expression
  , contextAssembleImplicitResource
      :: [Expression]
      -> Either SyntaxRewriteFailure Expression
  , contextAssembleExpansion
      :: SyntaxFunctionExpansion
      -> [Expression]
      -> Either SyntaxRewriteFailure Expression
  , contextPublish :: Expression -> Maybe SyntaxContext
  , contextRecursive :: [Expression] -> SyntaxContext
  , contextScope :: Expression -> SyntaxContext
  , contextEnter :: Maybe Expression -> SyntaxContext
  }

data RewriteRule = RewriteRule
  { rewriteRule :: SyntaxRule
  , rewriteRuleBranch :: Int
  , rewriteRuleLiteralPrefix :: [String]
  , rewriteRuleLiterals :: Set.Set String
  , rewriteRuleEvaluation :: Maybe (Expression -> Maybe InterpretedValue)
  , rewriteRuleHoleFamilies :: [Maybe InterpretedValue]
  , rewriteRuleSyntaxInsertion :: Maybe SyntaxFunctionInsertion
  , rewriteRuleReturnType :: Maybe InterpretedValue
  }

newtype RewriteNodeId = RewriteNodeId Int
  deriving (Eq, Ord, Show)

newtype SequenceId = SequenceId Int
  deriving (Eq, Ord, Show)

data RewriteDependency
  = RewriteNodeResult RewriteNodeId
  | SequenceDeclarations SequenceId
  deriving (Eq, Ord, Show)

-- | One structurally possible interpretation, before any capture is typed.
-- The list order produced by the candidate enumerator is the complete greedy
-- backtracking order and is therefore retained verbatim by a rewrite node.
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

-- | The concrete expansion produced once a candidate's captures and return
-- type are fixed. Nested block work is scheduled from this value before the
-- candidate is accepted; finalization only attaches the stored remainder.
data PreparedExpansion = PreparedExpansion
  { preparedExpansionSyntax :: SyntaxFunctionExpansion
  , preparedExpansionRemaining :: [Expression]
  }

-- | Persistent type inference accumulated while a candidate frame is below
-- child work on the stack.  Entries are indexed by template capture position;
-- advancing a frame never removes or recomputes an earlier entry.
data CandidateTypingContext = CandidateTypingContext
  { candidateTypingInputs :: Map Int InterpretedValue
  , candidateTypingExpectedHoles :: Map Int InterpretedValue
  , candidateTypingReturnType :: Maybe InterpretedValue
  }

data CandidateFrame = CandidateFrame
  { candidateFrameCandidate :: StructuralCandidate
  , candidateFrameNextCapture :: Int
  , candidateFrameTypingContext :: CandidateTypingContext
  , candidateFrameChildren :: Map Int RewriteNodeId
  , candidateFramePreparedCaptures :: Map Int Expression
  }

data CandidateFrameProgress
  = CandidateFrameNeedsChild
      Int
      (SyntaxHoleKind Expression)
      Expression
  | CandidateFrameBlocked (Set RewriteDependency)
  | CandidateFrameRejected CandidateRejectionDetails
  | CandidateFrameAccepted
      CandidateTypingContext
      [RewriteResult]
      InterpretedValue

data CandidateContinuation = CandidateContinuation
  { continuationParentNode :: RewriteNodeId
  , continuationCandidateCursor :: Int
  , continuationCaptureIndex :: Int
  }
  deriving (Eq, Ord, Show)

data RewriteParent
  = RewriteRoot
  | RewriteCandidateParent CandidateContinuation
  | RewriteOrdinaryParent RewriteNodeId
  | RewriteSequenceParent SequenceId
  deriving (Eq, Ord, Show)

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

data CandidateAttempt
  = CandidateAccepted SelectedCandidate
  | CandidateBlocked
      StructuralCandidate
      CandidateFrame
      (Set RewriteDependency)
  | CandidateRejected CandidateRejection

data RewriteResult = RewriteResult
  { rewriteResultExpression :: Expression
  , rewriteResultType :: Maybe InterpretedValue
  , rewriteResultSelection :: Maybe SelectedCandidate
  }

data RewriteNodeState
  = NodePending
  | NodeActive
  | NodeWaiting (Set RewriteDependency)
  | NodeFinalized RewriteResult

-- The environment is parameterized so the state model remains below the
-- application-specific callbacks used by SyntaxRewriting.
data RewriteNode environment = RewriteNode
  { rewriteNodeId :: RewriteNodeId
  , rewriteNodeSource :: Expression
  , rewriteNodeEnvironment :: environment
  , rewriteNodeCandidates :: [StructuralCandidate]
  , rewriteNodeAttempts :: [CandidateAttempt]
  , rewriteNodeCandidateCursor :: Int
  , rewriteNodeParent :: RewriteParent
  , rewriteNodeExpression :: Expression
  , rewriteNodeOrdinaryCursor :: Int
  , rewriteNodeOrdinaryChild :: Maybe RewriteNodeId
  , rewriteNodeOrdinaryResult :: Maybe RewriteResult
  , rewriteNodeState :: RewriteNodeState
  }

data SequenceFrame environment = SequenceFrame
  { sequenceFrameId :: SequenceId
  , sequenceFrameOwner :: RewriteNodeId
  , sequenceFrameSource :: Expression
  , sequenceFrameNodes :: [RewriteNodeId]
  , sequenceFrameInitialEnvironment :: environment
  , sequenceFrameEnvironment :: environment
  , sequenceFrameCursor :: Int
  , sequenceFrameResults :: Map RewriteNodeId RewriteResult
  , sequenceFrameDeclarationsComplete :: Bool
  , sequenceFrameExpansion :: Maybe (SelectedCandidate, PreparedExpansion)
  }

data RewriteTask
  = EnterNode RewriteNodeId
  | TryCandidate RewriteNodeId Int
  | ResumeCandidate RewriteNodeId Int
  | ResumeOrdinary RewriteNodeId
  | EnterSequence SequenceId
  | ResumeSequence SequenceId RewriteNodeId
  | ResumeSequenceDeclarations SequenceId RewriteNodeId
  | FinalizeSequence SequenceId
