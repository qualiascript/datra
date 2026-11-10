module SyntaxRewriting.Stack
  ( RewriteStackOperations (..)
  , runRewriteStack
  ) where

import Control.Monad.Trans.State.Strict (runState, state)
import Data.List.NonEmpty (NonEmpty (..))
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import DatraLanguage.AST
  ( Expression, expressionChildren, traverseExpressionChildren )
import DatraLanguage.StringExpression
  ( StringExpression, TemplateSelection (..) )
import DatraTypes (InterpretedValue)
import SyntaxRewriting.Candidates
  ( advanceCandidateFrameWith, initialCandidateFrame )
import SyntaxRewriting.Types
  ( CandidateFrame (..)
  , CandidateFrameProgress (..)
  , CandidateRejection
  , CandidateRejectionDetails (..)
  , CandidateSearch (..)
  , CandidateTypingContext
  , OrdinaryTraversal (..)
  , PreparedExpansion (..)
  , RewriteNode (..)
  , RewriteNodeId (..)
  , RewriteNodeState (..)
  , RewriteLocus (..)
  , RewriteResult (..)
  , RewriteWork (..)
  , SelectedCandidate (..)
  , StructuralCandidate (..)
  )

data RewriteStackOperations environment failure = RewriteStackOperations
  { stackEnumerateCandidates
      :: environment -> Expression -> [StructuralCandidate]
  , stackCaptureHole
      :: environment
      -> StructuralCandidate
      -> [(StringExpression Expression, Expression)]
      -> StringExpression Expression
      -> Expression
      -> Maybe Expression
  , stackExpectedHole
      :: environment
      -> StructuralCandidate
      -> CandidateTypingContext
      -> Int
      -> Maybe InterpretedValue
  , stackCandidateReturn
      :: environment
      -> StructuralCandidate
      -> CandidateTypingContext
      -> Maybe InterpretedValue
  , stackTypesCompatible
      :: InterpretedValue -> InterpretedValue -> Bool
  , stackRewriteScope
      :: environment -> RewriteLocus -> environment
  , stackFinalizeOrdinary
      :: environment -> Expression -> Either failure RewriteResult
  , stackPublishChild
      :: environment
      -> Expression
      -> Int
      -> RewriteResult
      -> Either failure (Maybe environment)
  , stackPrepareCandidate
      :: environment -> SelectedCandidate -> PreparedExpansion
  , stackExpandCandidate
      :: environment -> PreparedExpansion -> Either failure Expression
  , stackCandidateRejection
      :: environment
      -> CandidateRejectionDetails
      -> [CandidateRejection]
      -> CandidateRejection
  }

newtype RewriteMachine environment = RewriteMachine
  { machineNodes :: Map RewriteNodeId (RewriteNode environment) }

initialMachine
  :: environment
  -> Expression
  -> (RewriteNodeId, RewriteMachine environment)
initialMachine environment source = (rootId,
  RewriteMachine (Map.singleton rootId root))
  where
    rootId = nextNodeId Map.empty
    root = RewriteNode
      { rewriteNodeExpression = source
      , rewriteNodeEnvironment = environment
      , rewriteNodeParent = Nothing
      , rewriteNodeRejections = []
      , rewriteNodeState = NodePending
      }

nodeAt
  :: RewriteNodeId
  -> RewriteMachine environment
  -> RewriteNode environment
nodeAt nodeId = (Map.! nodeId) . machineNodes

updateNode
  :: RewriteNodeId
  -> (RewriteNode environment -> RewriteNode environment)
  -> RewriteMachine environment
  -> RewriteMachine environment
updateNode nodeId update machine = machine
  { machineNodes = Map.adjust update nodeId (machineNodes machine) }

allocateNode
  :: Expression
  -> environment
  -> Maybe RewriteNodeId
  -> RewriteMachine environment
  -> (RewriteNodeId, RewriteMachine environment)
allocateNode source environment parent machine =
  (nodeId, machine
    { machineNodes = Map.insert nodeId node (machineNodes machine) })
  where
    nodeId = nextNodeId (machineNodes machine)
    node = RewriteNode
      { rewriteNodeExpression = source
      , rewriteNodeEnvironment = environment
      , rewriteNodeParent = parent
      , rewriteNodeRejections = []
      , rewriteNodeState = NodePending
      }

nextNodeId :: Map RewriteNodeId node -> RewriteNodeId
nextNodeId = RewriteNodeId . Map.size

-- | The scheduler stack contains node IDs only.  Every continuation is read
-- from the popped node's stored state.
runRewriteStack
  :: RewriteStackOperations environment failure
  -> environment
  -> Expression
  -> Either failure (RewriteResult, [CandidateRejection])
runRewriteStack operations initialEnvironment source =
  run (rootId :| []) allocated
  where
    rootEnvironment = stackRewriteScope operations initialEnvironment
      (RewriteExpression source)
    (rootId, allocated) = initialMachine rootEnvironment source

    run (nodeId :| stack) machine =
      case rewriteNodeState (nodeAt nodeId machine) of
        NodePending -> enterNode nodeId stack machine
        NodeReady work -> runReady nodeId work stack machine
        NodeWaiting work child -> resumeNode nodeId work child stack machine
        NodeFinalized result -> case rewriteNodeParent (nodeAt nodeId machine) of
          Nothing -> Right
            (result, rewriteNodeRejections (nodeAt nodeId machine))
          Just parent -> run (parent :| stack) machine

    enterNode nodeId stack machine =
      let node = nodeAt nodeId machine
          environment = rewriteNodeEnvironment node
          candidates = stackEnumerateCandidates operations environment
            (rewriteNodeExpression node)
          ready
            | null candidates = TraverseChildren (ordinary Nothing)
            | otherwise = SearchCandidates CandidateSearch
                { candidateSearchCandidates = candidates
                , candidateSearchCursor = 0
                , candidateSearchRejections = []
                , candidateSearchFrame = Nothing
                }
          entered = updateNode nodeId
            (\current -> current { rewriteNodeState = NodeReady ready }) machine
      in run (nodeId :| stack) entered

    ordinary selection = OrdinaryTraversal
      { ordinaryTraversalCursor = 0
      , ordinaryTraversalSelection = selection
      , ordinaryTraversalFinalizedCaptures = maybe []
          (concatMap expressionClosure
            . map rewriteResultExpression . selectedCaptures) selection
      }

    expressionClosure value = value : concatMap expressionClosure
      (expressionChildren value)

    runReady nodeId work stack machine = case work of
      SearchCandidates search -> searchCandidate nodeId search stack machine
      TraverseChildren traversal ->
        traverseOrdinary nodeId traversal stack machine

    searchCandidate nodeId search stack machine =
      case drop (candidateSearchCursor search)
          (candidateSearchCandidates search) of
        [] ->
          let traversal = ordinary Nothing
              advanced = updateNode nodeId (\current -> current
                { rewriteNodeRejections = candidateSearchRejections search
                , rewriteNodeState = NodeReady (TraverseChildren traversal)
                }) machine
          in run (nodeId :| stack) advanced
        candidate : _ ->
          let node = nodeAt nodeId machine
              environment = rewriteNodeEnvironment node
              frame = maybe (initialCandidateFrame candidate) id
                (candidateSearchFrame search)
              progress = advanceCandidateFrameWith
                (stackCaptureHole operations environment candidate)
                (stackExpectedHole operations environment candidate)
                (stackCandidateReturn operations environment candidate)
                (stackTypesCompatible operations)
                candidate frame
          in case progress of
            CandidateFrameNeedsChild progressed _ _ childSource ->
              allocateChild nodeId (SearchCandidates search
                { candidateSearchFrame = Just progressed }) childSource
                (RewriteExpression childSource) stack machine
            CandidateFrameRejected details ->
              let childRejections = concatMap rewriteNodeRejections
                    [ child
                    | child <- Map.elems (machineNodes machine)
                    , rewriteNodeParent child == Just nodeId
                    ]
                  rejection = stackCandidateRejection operations
                    environment details childRejections
                  advancedSearch = search
                    { candidateSearchCursor = candidateSearchCursor search + 1
                    , candidateSearchRejections =
                        candidateSearchRejections search <> [rejection]
                    , candidateSearchFrame = Nothing
                    }
                  advanced = updateNode nodeId (\current -> current
                    { rewriteNodeState = NodeReady
                        (SearchCandidates advancedSearch) }) machine
              in run (nodeId :| stack) advanced
            CandidateFrameAccepted _ captureResults returnType -> do
              let rewrittenCaptures = map rewriteResultExpression captureResults
                  selection = (structuralCandidateSelection candidate)
                    { templateSelectionCaptures = rewrittenCaptures }
                  selected = SelectedCandidate
                    { selectedStructuralCandidate = candidate
                        { structuralCandidateSelection = selection }
                    , selectedCaptures = captureResults
                    , selectedReturnType = returnType
                    }
                  prepared = stackPrepareCandidate operations environment selected
              expanded <- stackExpandCandidate operations environment prepared
              let traversal = ordinary (Just selected)
                  transitioned = replaceNodeEnvironment nodeId
                    (stackRewriteScope operations environment
                      (RewriteExpression expanded)) machine
                  advanced = updateNode nodeId (\current -> current
                    { rewriteNodeExpression = expanded
                    , rewriteNodeRejections = candidateSearchRejections search
                    , rewriteNodeState = NodeReady
                        (TraverseChildren traversal)
                    }) transitioned
              run (nodeId :| stack) advanced

    allocateChild parentId work childSource locus stack machine =
      let parent = nodeAt parentId machine
          parentEnvironment = rewriteNodeEnvironment parent
          childEnvironment = stackRewriteScope operations
            parentEnvironment locus
          (childId, allocatedChild) = allocateNode childSource childEnvironment
            (Just parentId) machine
          waiting = updateNode parentId (\current -> current
            { rewriteNodeState = NodeWaiting work childId })
            allocatedChild
      in run (childId :| stack) waiting

    resumeNode nodeId work childId stack machine =
      case rewriteNodeState (nodeAt childId machine) of
        NodeFinalized childResult -> case work of
          SearchCandidates search ->
            let frame = maybe
                  (initialCandidateFrame
                    (candidateSearchCandidates search !!
                      candidateSearchCursor search))
                  id (candidateSearchFrame search)
                index = candidateFrameNextCapture frame
                consumed = frame
                  { candidateFrameResults = Map.insert index childResult
                      (candidateFrameResults frame) }
                readySearch = search { candidateSearchFrame = Just consumed }
                ready = updateNode nodeId (\current -> current
                  { rewriteNodeState = NodeReady
                      (SearchCandidates readySearch) }) machine
            in run (nodeId :| stack) ready
          TraverseChildren traversal -> do
            let node = nodeAt nodeId machine
                environment = rewriteNodeEnvironment node
                cursor = ordinaryTraversalCursor traversal
            let installed = fst (runState
                  (traverseExpressionChildren
                    (\child -> state $ \index ->
                      ( if index == cursor
                          then rewriteResultExpression childResult
                          else child
                      , index + 1
                      ))
                  (rewriteNodeExpression node)) 0)
            publication <- stackPublishChild operations environment
              installed cursor childResult
            let published = case publication of
                  Nothing -> machine
                  Just nextEnvironment -> updateNode nodeId (\current -> current
                    { rewriteNodeEnvironment = nextEnvironment }) machine
                advancedTraversal = traversal
                  { ordinaryTraversalCursor = cursor + 1 }
                ready = updateNode nodeId (\current -> current
                  { rewriteNodeExpression = installed
                  , rewriteNodeState = NodeReady
                      (TraverseChildren advancedTraversal) }) published
            run (nodeId :| stack) ready
        _ -> run (childId :| stack) machine

    traverseOrdinary nodeId traversal stack machine =
      let node = nodeAt nodeId machine
          environment = rewriteNodeEnvironment node
          cursor = ordinaryTraversalCursor traversal
          children = expressionChildren (rewriteNodeExpression node)
      in case listAt cursor children of
        Nothing -> do
          ordinaryResult <- stackFinalizeOrdinary operations environment
            (rewriteNodeExpression node)
          let result = case ordinaryTraversalSelection traversal of
                Nothing -> ordinaryResult
                Just selected -> ordinaryResult
                  { rewriteResultType = Just (selectedReturnType selected)
                  , rewriteResultSelection = Just selected
                  }
              finalized = updateNode nodeId (\current -> current
                { rewriteNodeState = NodeFinalized result }) machine
          case rewriteNodeParent node of
            Nothing -> run (nodeId :| stack) finalized
            Just parent -> run (parent :| stack) finalized
        Just childSource
          | childSource `elem` ordinaryTraversalFinalizedCaptures traversal ->
              let remaining = removeFirst childSource
                    (ordinaryTraversalFinalizedCaptures traversal)
                  advanced = traversal
                    { ordinaryTraversalCursor = cursor + 1
                    , ordinaryTraversalFinalizedCaptures = remaining
                    }
                  ready = updateNode nodeId (\current -> current
                    { rewriteNodeState = NodeReady
                        (TraverseChildren advanced) }) machine
              in run (nodeId :| stack) ready
          | otherwise ->
              allocateChild nodeId (TraverseChildren traversal)
                childSource
                (RewriteChild (rewriteNodeExpression node) cursor childSource)
                stack machine

    listAt selected = listHead . drop selected
    listHead [] = Nothing
    listHead (selected : _) = Just selected

    removeFirst _ [] = []
    removeFirst selected (value : values)
      | selected == value = values
      | otherwise = value : removeFirst selected values

    replaceNodeEnvironment nodeId selected = updateNode nodeId (\node -> node
      { rewriteNodeEnvironment = selected })
