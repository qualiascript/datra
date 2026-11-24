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
import StringExpression
  ( TemplateSelection (..) )
import StringInterpolation (DeclarativeCapture)
import SyntaxRewriting.Candidates
  ( advanceCandidateFrameWith, initialCandidateFrame )
import SyntaxRewriting.Types
  ( CandidateFrame (..)
  , CandidateFrameProgress (..)
  , CandidatePreparation (..)
  , CandidateRejection
  , CandidateRejectionReason (..)
  , CandidateRejectionDetails (..)
  , CandidateSearch (..)
  , CandidateTypingContext (..)
  , Compatibility (..)
  , CompatibilityConstraint (..)
  , OrdinaryTraversal (..)
  , PreparedExpansion (..)
  , RewriteNode (..)
  , RewriteNodeId (..)
  , RewriteNodeState (..)
  , RewriteLocus (..)
  , RewriteResult (..)
  , RewriteRule (..)
  , RewriteWork (..)
  , SelectedCandidate (..)
  , StructuralCandidate (..)
  )

data RewriteStackOperations environment failure syntaxType = RewriteStackOperations
  { stackEnumerateCandidates
      :: environment -> Expression -> [StructuralCandidate syntaxType]
  , stackPostRewrite
      :: environment -> Expression -> Maybe Expression
  , stackPrepareStructuralCapture
      :: DeclarativeCapture
      -> Expression
      -> Maybe Expression
  , stackExpectedHole
      :: environment
      -> StructuralCandidate syntaxType
      -> CandidateTypingContext syntaxType
      -> Int
      -> Maybe syntaxType
  , stackCandidateReturn
      :: environment
      -> StructuralCandidate syntaxType
      -> CandidateTypingContext syntaxType
      -> syntaxType
  , stackTypesCompatible
      :: environment -> syntaxType -> syntaxType -> Compatibility
  , stackRewriteScope
      :: environment -> RewriteLocus -> environment
  , stackFinalizeOrdinary
      :: environment
      -> Expression
      -> Either failure (RewriteResult syntaxType)
  , stackPublishChild
      :: environment
      -> Expression
      -> Int
      -> RewriteResult syntaxType
      -> Either failure (Maybe environment)
  , stackPrepareCandidate
      :: environment
      -> SelectedCandidate syntaxType
      -> CandidatePreparation
  , stackExpandCandidate
      :: environment -> PreparedExpansion -> Either failure Expression
  , stackCandidateRejection
      :: environment
      -> CandidateRejectionDetails syntaxType
      -> [CandidateRejection syntaxType]
      -> CandidateRejection syntaxType
  }

newtype RewriteMachine environment syntaxType = RewriteMachine
  { machineNodes
      :: Map RewriteNodeId (RewriteNode environment syntaxType) }

initialMachine
  :: environment
  -> Expression
  -> (RewriteNodeId, RewriteMachine environment syntaxType)
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
  -> RewriteMachine environment syntaxType
  -> RewriteNode environment syntaxType
nodeAt nodeId = (Map.! nodeId) . machineNodes

updateNode
  :: RewriteNodeId
  -> (RewriteNode environment syntaxType -> RewriteNode environment syntaxType)
  -> RewriteMachine environment syntaxType
  -> RewriteMachine environment syntaxType
updateNode nodeId update machine = machine
  { machineNodes = Map.adjust update nodeId (machineNodes machine) }

allocateNode
  :: Expression
  -> environment
  -> Maybe RewriteNodeId
  -> RewriteMachine environment syntaxType
  -> (RewriteNodeId, RewriteMachine environment syntaxType)
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
  :: RewriteStackOperations environment failure syntaxType
  -> environment
  -> Expression
  -> Either failure
      (RewriteResult syntaxType, [CandidateRejection syntaxType])
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
      in case candidates of
        [] -> continueAfterCandidates nodeId
          (rewriteNodeRejections node) stack machine
        _ ->
          let ready = SearchCandidates CandidateSearch
                { candidateSearchCandidates = candidates
                , candidateSearchCursor = 0
                , candidateSearchRejections = []
                , candidateSearchFrame = Nothing
                }
              entered = updateNode nodeId
                (\current -> current { rewriteNodeState = NodeReady ready })
                machine
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
        [] -> continueAfterCandidates nodeId
          (candidateSearchRejections search) stack machine
        candidate : _ ->
          let node = nodeAt nodeId machine
              environment = rewriteNodeEnvironment node
              frame = maybe (initialCandidateFrame candidate) id
                (candidateSearchFrame search)
              progress = advanceCandidateFrameWith
                (stackPrepareStructuralCapture operations)
                (stackExpectedHole operations environment candidate)
                (stackCandidateReturn operations environment candidate)
                (stackTypesCompatible operations environment)
                candidate frame
          in case progress of
            CandidateFrameNeedsChild progressed _ _ childSource ->
              allocateChild nodeId (SearchCandidates search
                { candidateSearchFrame = Just progressed }) childSource
                (RewriteExpression childSource) stack machine
            CandidateFrameNeedsTerminal progressed index _ terminalSource -> do
              terminalResult <- stackFinalizeOrdinary operations environment
                terminalSource
              let consumed = progressed
                    { candidateFrameResults = Map.insert index terminalResult
                        (candidateFrameResults progressed) }
                  readySearch = search
                    { candidateSearchFrame = Just consumed }
                  ready = updateNode nodeId (\current -> current
                    { rewriteNodeState = NodeReady
                        (SearchCandidates readySearch) }) machine
              run (nodeId :| stack) ready
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
            CandidateFrameComplete typingContext captureResults returnType -> do
              let rewrittenCaptures = map rewriteResultExpression captureResults
                  selection = (structuralCandidateSelection candidate)
                    { templateSelectionCaptures = rewrittenCaptures }
                  selected = SelectedCandidate
                    { selectedStructuralCandidate = candidate
                        { structuralCandidateSelection = selection }
                    , selectedCaptures = captureResults
                    , selectedReturnType = returnType
                    , selectedTypingContext = typingContext
                    }
                  preparation = stackPrepareCandidate operations
                    environment selected
              case preparation of
                CandidateInapplicable ->
                  advanceCandidateSearch nodeId search stack machine
                CandidatePrepared prepared validated ->
                  decidePreparedCandidate nodeId search selected prepared
                    validated stack machine

    decidePreparedCandidate nodeId search selected prepared validated stack
        machine =
      case (refuted, undecidable) of
        (constraint : _, _) -> rejectConstraint
          TypedHoleMismatch constraint
        (_, constraint : _) -> rejectConstraint
          CandidateCompatibilityUndecidable constraint
        _ -> do
          expanded <- stackExpandCandidate operations environment prepared
          let resolvedContext = (selectedTypingContext selected)
                { candidateTypingBlocked = [] }
              resolved = selected
                { selectedTypingContext = resolvedContext }
              traversal = ordinary (Just resolved)
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
      where
        node = nodeAt nodeId machine
        environment = rewriteNodeEnvironment node
        remaining = filter
          ((`notElem` validated) . compatibilityCaptureIndex)
          (candidateTypingBlocked (selectedTypingContext selected))
        decisions =
          [ (constraint, stackTypesCompatible operations environment
              (compatibilitySource constraint)
              (compatibilityTarget constraint))
          | constraint <- remaining
          ]
        refuted = [constraint | (constraint, CompatibilityRefuted) <- decisions]
        undecidable =
          [constraint | (constraint, CompatibilityUndecidable) <- decisions]
        rejectConstraint reason constraint =
          let candidate = selectedStructuralCandidate selected
              details = CandidateRejectionDetails
                { candidateRejectionRule = structuralCandidateRule candidate
                , candidateRejectionBranch = rewriteRuleBranch
                    (structuralCandidateRule candidate)
                , candidateRejectionCaptureIndex =
                    compatibilityCaptureIndex constraint
                , candidateRejectionSource = templateSelectionWhole
                    (structuralCandidateSelection candidate)
                , candidateRejectionExpected = Just
                    (compatibilityTarget constraint)
                , candidateRejectionActual = Just
                    (compatibilitySource constraint)
                , candidateRejectionContext = selectedTypingContext selected
                , candidateRejectionReason = reason
                }
              childRejections = concatMap rewriteNodeRejections
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

    advanceCandidateSearch nodeId search stack machine =
      let advancedSearch = search
            { candidateSearchCursor = candidateSearchCursor search + 1
            , candidateSearchFrame = Nothing
            }
          advanced = updateNode nodeId (\current -> current
            { rewriteNodeState = NodeReady
                (SearchCandidates advancedSearch) }) machine
      in run (nodeId :| stack) advanced

    continueAfterCandidates nodeId rejections stack machine =
      let node = nodeAt nodeId machine
          environment = rewriteNodeEnvironment node
          currentExpression = rewriteNodeExpression node
      in case stackPostRewrite operations environment currentExpression of
        Just rewritten
          | rewritten /= currentExpression ->
              let advanced = updateNode nodeId (\current -> current
                    { rewriteNodeExpression = rewritten
                    , rewriteNodeRejections = []
                    , rewriteNodeState = NodeReady
                        (TraverseChildren (ordinary Nothing))
                    }) machine
              in run (nodeId :| stack) advanced
        _ ->
          let traversal = ordinary Nothing
              advanced = updateNode nodeId (\current -> current
                { rewriteNodeRejections = rejections
                , rewriteNodeState = NodeReady (TraverseChildren traversal)
                }) machine
          in run (nodeId :| stack) advanced

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
                  { rewriteResultType = selectedReturnType selected
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
