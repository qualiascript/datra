module SyntaxRewriting.Stack
  ( RewriteStackOperations (..)
  , runRewriteStack
  ) where

import Control.Monad.Trans.State.Strict (runState, state)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import DatraLanguage.AST
  ( Expression, expressionChildren, traverseExpressionChildren )
import StringExpression
  ( TemplateSelection (..) )
import StringInterpolation (DeclarativeCapture)
import DatraTypes (InterpretedValue)
import DatraTypes.Scope
  ( DeclarationLayerImportPolicy (StrictImport) )
import SyntaxRewriting.Candidates
  ( advanceCandidateFrameWith, initialCandidateFrame )
import SyntaxRewriting.Types
  ( CandidateFrame (..)
  , CandidateDecision (..)
  , CandidateFrameProgress (..)
  , CandidateRejection
  , CandidateRejectionReason (..)
  , CandidateRejectionDetails (..)
  , CandidateSearch (..)
  , CandidateTypingContext (..)
  , HeldCandidate (..)
  , OrdinaryTraversal (..)
  , PreparedExpansion (..)
  , ProvisionalCandidate (..)
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

data RewriteStackOperations environment failure = RewriteStackOperations
  { stackExhausted :: failure
  , stackEnumerateCandidates
      :: environment -> Expression -> [StructuralCandidate]
  , stackPostRewrite
      :: environment -> Expression -> Maybe Expression
  , stackPrepareStructuralCapture
      :: DeclarativeCapture
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
  , stackDecideCandidate
      :: environment
      -> SelectedCandidate
      -> CandidateDecision
  , stackBlockerResolved
      :: environment -> Expression -> Bool
  , stackRewriteScope
      :: environment -> RewriteLocus -> environment
  , stackFinalizeOrdinary
      :: environment
      -> Expression
      -> Either failure RewriteResult
  , stackPublishChild
      :: environment
      -> Expression
      -> Int
      -> RewriteResult
      -> Either failure (Maybe environment)
  , stackPrepareCandidate
      :: environment
      -> SelectedCandidate
      -> PreparedExpansion
  , stackExpandCandidate
      :: environment -> PreparedExpansion -> Either failure Expression
  , stackCandidateRejection
      :: environment
      -> CandidateRejectionDetails
      -> [CandidateRejection]
      -> CandidateRejection
  , stackStrictImportAmbiguity
      :: environment -> Expression -> failure
  }

data RewriteMachine environment = RewriteMachine
  { machineNodes :: Map RewriteNodeId (RewriteNode environment)
  , machineBlocked :: Map Expression (Set RewriteNodeId)
  }

initialMachine
  :: environment
  -> Expression
  -> (RewriteNodeId, RewriteMachine environment)
initialMachine environment source = (rootId,
  RewriteMachine (Map.singleton rootId root) Map.empty)
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
  run [rootId] allocated
  where
    rootEnvironment = stackRewriteScope operations initialEnvironment
      (RewriteExpression source)
    (rootId, allocated) = initialMachine rootEnvironment source

    run [] machine = settleBlocked machine
    run (nodeId : stack) machine =
      case rewriteNodeState (nodeAt nodeId machine) of
        NodePending -> enterNode nodeId stack machine
        NodeReady work -> runReady nodeId work stack machine
        NodeWaiting work child -> resumeNode nodeId work child stack machine
        NodeHeld _ -> run stack machine
        NodeFinalized result -> case rewriteNodeParent (nodeAt nodeId machine) of
          Nothing -> Right
            (result, rewriteNodeRejections (nodeAt nodeId machine))
          Just parent -> run (parent : stack) machine

    settleBlocked machine = case
        [ (nodeId, held)
        | (nodeId, node) <- Map.toAscList (machineNodes machine)
        , NodeHeld held <- [rewriteNodeState node]
        ] of
      [] -> Left (stackExhausted operations)
      (nodeId, held) : _ ->
        rejectHeldCandidate nodeId held [] (unregisterNode nodeId machine)

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
                , candidateSearchProvisional = Nothing
                }
              entered = updateNode nodeId
                (\current -> current { rewriteNodeState = NodeReady ready })
                machine
          in run (nodeId : stack) entered

    ordinary selection = OrdinaryTraversal
      { ordinaryTraversalCursor = 0
      , ordinaryTraversalSelection = selection
      , ordinaryTraversalFinalizedCaptures = Map.fromListWith (+)
          [ (expressionValue, 1)
          | expressionValue <- maybe []
              (concatMap (expressionClosure . rewriteResultExpression)
                . selectedCaptures) selection
          ]
      , ordinaryTraversalPending = Map.empty
      }

    expressionClosure expressionValue = expressionValue :
      concatMap expressionClosure (expressionChildren expressionValue)

    runReady nodeId work stack machine = case work of
      SearchCandidates search -> searchCandidate nodeId search stack machine
      DecideCandidate held -> decideHeldCandidate nodeId held stack machine
      TraverseChildren traversal ->
        traverseOrdinary nodeId traversal stack machine

    searchCandidate nodeId search stack machine =
      case drop (candidateSearchCursor search)
          (candidateSearchCandidates search) of
        [] -> case candidateSearchProvisional search of
          Nothing -> continueAfterCandidates nodeId
            (candidateSearchRejections search) stack machine
          Just provisional -> commitAcceptedCandidate
            nodeId
            search
            (provisionalCandidateSelected provisional)
            (provisionalCandidatePrepared provisional)
            (provisionalCandidateReturnType provisional)
            stack
            machine
        candidate : _ ->
          if not (candidateEligible search candidate)
            then searchCandidate nodeId search
              { candidateSearchCursor = candidateSearchCursor search + 1
              , candidateSearchFrame = Nothing
              } stack machine
            else
              let node = nodeAt nodeId machine
                  environment = rewriteNodeEnvironment node
                  frame = maybe (initialCandidateFrame candidate) id
                    (candidateSearchFrame search)
                  progress = advanceCandidateFrameWith
                    (stackPrepareStructuralCapture operations)
                    (stackExpectedHole operations environment candidate)
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
                  run (nodeId : stack) ready
                CandidateFrameRejected details ->
                  let childRejections = concatMap rewriteNodeRejections
                        [ child
                        | child <- Map.elems (machineNodes machine)
                        , rewriteNodeParent child == Just nodeId
                        ]
                      rejection = stackCandidateRejection operations
                        environment details childRejections
                      advancedSearch = search
                        { candidateSearchCursor =
                            candidateSearchCursor search + 1
                        , candidateSearchRejections =
                            candidateSearchRejections search <> [rejection]
                        , candidateSearchFrame = Nothing
                        }
                      advanced = updateNode nodeId (\current -> current
                        { rewriteNodeState = NodeReady
                            (SearchCandidates advancedSearch) }) machine
                  in run (nodeId : stack) advanced
                CandidateFrameComplete typingContext captureResults -> do
                  let rewrittenCaptures =
                        map rewriteResultExpression captureResults
                      selection = (structuralCandidateSelection candidate)
                        { templateSelectionCaptures = rewrittenCaptures }
                      selected = SelectedCandidate
                        { selectedStructuralCandidate = candidate
                            { structuralCandidateSelection = selection }
                        , selectedCaptures = captureResults
                        , selectedReturnType = stackCandidateReturn operations
                            environment candidate typingContext
                        , selectedTypingContext = typingContext
                        }
                      prepared = stackPrepareCandidate operations
                        environment selected
                  decidePreparedCandidate nodeId search selected prepared
                    stack machine

    decidePreparedCandidate nodeId search selected prepared stack
        machine = decideHeldCandidate nodeId held stack machine
      where
        held = HeldCandidate
          { heldCandidateSearch = search
          , heldCandidateSelected = selected
          , heldCandidatePrepared = prepared
          , heldCandidateBlockers = []
          , heldCandidateFallback = fallbackDetails selected
          }

    decideHeldCandidate nodeId held stack machine =
      case stackDecideCandidate operations environment
          (heldCandidateSelected held) of
        CandidateAccepted returnType ->
          acceptCandidate nodeId held returnType stack machine
        CandidateHeld blockers fallback
          | null blockers -> rejectHeldCandidate nodeId
              held { heldCandidateFallback = fallback } stack machine
          | otherwise ->
              let suspended = held
                    { heldCandidateBlockers = blockers
                    , heldCandidateFallback = fallback
                    }
                  registered = registerHeld nodeId suspended machine
              in run (maybe stack (: stack)
                    (rewriteNodeParent (nodeAt nodeId registered))) registered
        CandidateRefuted details -> rejectHeldCandidate nodeId
          held { heldCandidateFallback = details } stack machine
      where
        environment = rewriteNodeEnvironment (nodeAt nodeId machine)

    acceptCandidate nodeId held returnType stack machine =
      case candidateSearchProvisional search of
        Just _ -> Left (stackStrictImportAmbiguity operations environment
          (rewriteNodeExpression (nodeAt nodeId machine)))
        Nothing
          | rewriteRuleImportPolicy selectedRule == StrictImport ->
              let provisional = ProvisionalCandidate
                    { provisionalCandidateSelected = selected
                    , provisionalCandidatePrepared = prepared
                    , provisionalCandidateReturnType = returnType
                    }
                  advancedSearch = search
                    { candidateSearchCursor = candidateSearchCursor search + 1
                    , candidateSearchFrame = Nothing
                    , candidateSearchProvisional = Just provisional
                    }
                  advanced = updateNode nodeId (\current -> current
                    { rewriteNodeState = NodeReady
                        (SearchCandidates advancedSearch) })
                    (unregisterNode nodeId machine)
              in run (nodeId : stack) advanced
          | otherwise -> commitAcceptedCandidate nodeId search selected
              prepared returnType stack machine
      where
        environment = rewriteNodeEnvironment (nodeAt nodeId machine)
        search = heldCandidateSearch held
        selected = heldCandidateSelected held
        prepared = heldCandidatePrepared held
        selectedRule = structuralCandidateRule
          (selectedStructuralCandidate selected)

    commitAcceptedCandidate nodeId search selected prepared returnType stack
        machine = do
      let environment = rewriteNodeEnvironment (nodeAt nodeId machine)
      expanded <- stackExpandCandidate operations environment prepared
      let accepted = selected { selectedReturnType = Just returnType }
          traversal = ordinary (Just accepted)
          transitioned = replaceNodeEnvironment nodeId
            (stackRewriteScope operations environment
              (RewriteExpression expanded)) (unregisterNode nodeId machine)
          advanced = updateNode nodeId (\current -> current
            { rewriteNodeExpression = expanded
            , rewriteNodeRejections = candidateSearchRejections search
            , rewriteNodeState = NodeReady (TraverseChildren traversal)
            }) transitioned
      run (nodeId : stack) advanced

    candidateEligible search candidate =
      case candidateSearchProvisional search of
        Nothing -> True
        Just provisional ->
          rewriteRuleImportPolicy candidateRule == StrictImport
            && rewriteRuleLayer candidateRule > rewriteRuleLayer selectedRule
          where
            candidateRule = structuralCandidateRule candidate
            selectedRule = structuralCandidateRule
              (selectedStructuralCandidate
                (provisionalCandidateSelected provisional))

    rejectHeldCandidate nodeId held stack machine =
      let environment = rewriteNodeEnvironment (nodeAt nodeId machine)
          childRejections = concatMap rewriteNodeRejections
            [ child
            | child <- Map.elems (machineNodes machine)
            , rewriteNodeParent child == Just nodeId
            ]
          rejection = stackCandidateRejection operations environment
            (heldCandidateFallback held) childRejections
          search = heldCandidateSearch held
          advancedSearch = search
            { candidateSearchCursor = candidateSearchCursor search + 1
            , candidateSearchRejections =
                candidateSearchRejections search <> [rejection]
            , candidateSearchFrame = Nothing
            }
          advanced = updateNode nodeId (\current -> current
            { rewriteNodeState = NodeReady
                (SearchCandidates advancedSearch) })
            (unregisterNode nodeId machine)
      in run (nodeId : stack) advanced

    fallbackDetails selected = CandidateRejectionDetails
      { candidateRejectionRule = structuralCandidateRule candidate
      , candidateRejectionBranch = rewriteRuleBranch
          (structuralCandidateRule candidate)
      , candidateRejectionCaptureIndex = 0
      , candidateRejectionSource = templateSelectionWhole
          (structuralCandidateSelection candidate)
      , candidateRejectionExpected = Nothing
      , candidateRejectionActual = Nothing
      , candidateRejectionContext = selectedTypingContext selected
      , candidateRejectionReason = TypedHoleMismatch
      }
      where
        candidate = selectedStructuralCandidate selected

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
              in run (nodeId : stack) advanced
        _ ->
          let traversal = ordinary Nothing
              advanced = updateNode nodeId (\current -> current
                { rewriteNodeRejections = rejections
                , rewriteNodeState = NodeReady (TraverseChildren traversal)
                }) machine
          in run (nodeId : stack) advanced

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
      in run (childId : stack) waiting

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
            in run (nodeId : stack) ready
          DecideCandidate held -> decideHeldCandidate nodeId held stack machine
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
            let (published, woken) = case publication of
                  Nothing -> (machine, [])
                  Just nextEnvironment ->
                    wakeResolved nextEnvironment
                      (updateNode nodeId (\current -> current
                        { rewriteNodeEnvironment = nextEnvironment }) machine)
                advancedTraversal = traversal
                  { ordinaryTraversalCursor = cursor + 1 }
                ready = updateNode nodeId (\current -> current
                  { rewriteNodeExpression = installed
                  , rewriteNodeState = NodeReady
                      (TraverseChildren advancedTraversal) }) published
            run (woken <> (nodeId : stack)) ready
        NodeHeld _ -> case work of
          TraverseChildren traversal ->
            let cursor = ordinaryTraversalCursor traversal
                advancedTraversal = traversal
                  { ordinaryTraversalCursor = cursor + 1
                  , ordinaryTraversalPending = Map.insert cursor childId
                      (ordinaryTraversalPending traversal)
                  }
                ready = updateNode nodeId (\current -> current
                  { rewriteNodeState = NodeReady
                      (TraverseChildren advancedTraversal) }) machine
            in run (nodeId : stack) ready
          _ -> run stack machine
        _ -> run (childId : stack) machine

    traverseOrdinary nodeId traversal stack machine =
      case finalizedPending traversal machine of
        Just (pendingCursor, childId, childResult) ->
          installPending nodeId traversal pendingCursor childId childResult
            stack machine
        Nothing -> traverseNext
      where
        node = nodeAt nodeId machine
        environment = rewriteNodeEnvironment node
        cursor = ordinaryTraversalCursor traversal
        children = expressionChildren (rewriteNodeExpression node)
        traverseNext =
          case listAt cursor children of
            Nothing
              | not (Map.null (ordinaryTraversalPending traversal)) ->
                  run stack machine
              | otherwise -> do
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
                    Nothing -> run (nodeId : stack) finalized
                    Just parent -> run (parent : stack) finalized
            Just childSource
              | Map.member childSource
                  (ordinaryTraversalFinalizedCaptures traversal) ->
                  let advancedTraversal = traversal
                        { ordinaryTraversalCursor = cursor + 1
                        , ordinaryTraversalFinalizedCaptures = Map.update
                            decrement childSource
                            (ordinaryTraversalFinalizedCaptures traversal)
                        }
                      ready = updateNode nodeId (\current -> current
                        { rewriteNodeState = NodeReady
                            (TraverseChildren advancedTraversal) }) machine
                  in run (nodeId : stack) ready
              | otherwise ->
                  allocateChild nodeId (TraverseChildren traversal)
                    childSource
                    (RewriteChild (rewriteNodeExpression node) cursor childSource)
                    stack machine

    finalizedPending traversal machine = listHead
      [ (cursor, childId, result)
      | (cursor, childId) <- Map.toAscList
          (ordinaryTraversalPending traversal)
      , NodeFinalized result <- [rewriteNodeState (nodeAt childId machine)]
      ]

    installPending nodeId traversal cursor _ childResult stack machine = do
      let node = nodeAt nodeId machine
          environment = rewriteNodeEnvironment node
          installed = installChild cursor childResult
            (rewriteNodeExpression node)
      publication <- stackPublishChild operations environment
        installed cursor childResult
      let withoutPending = traversal
            { ordinaryTraversalPending = Map.delete cursor
                (ordinaryTraversalPending traversal) }
          (published, woken) = case publication of
            Nothing -> (machine, [])
            Just nextEnvironment ->
              wakeResolved nextEnvironment
                (updateNode nodeId (\current -> current
                  { rewriteNodeEnvironment = nextEnvironment }) machine)
          ready = updateNode nodeId (\current -> current
            { rewriteNodeExpression = installed
            , rewriteNodeState = NodeReady
                (TraverseChildren withoutPending) }) published
      run (woken <> (nodeId : stack)) ready

    installChild cursor childResult expressionValue = fst (runState
      (traverseExpressionChildren
        (\child -> state $ \index ->
          ( if index == cursor
              then rewriteResultExpression childResult
              else child
          , index + 1
          ))
        expressionValue)
      0)

    decrement count
      | count <= 1 = Nothing
      | otherwise = Just (count - 1)

    registerHeld nodeId held machine =
      let cleared = unregisterNode nodeId machine
          indexed = foldr
            (\blocker -> Map.insertWith Set.union blocker (Set.singleton nodeId))
            (machineBlocked cleared)
            (heldCandidateBlockers held)
      in (updateNode nodeId (\node -> node
            { rewriteNodeState = NodeHeld held }) cleared)
          { machineBlocked = indexed }

    unregisterNode nodeId machine = machine
      { machineBlocked = foldr remove
          (machineBlocked machine) blockers }
      where
        blockers = case rewriteNodeState (nodeAt nodeId machine) of
          NodeHeld held -> heldCandidateBlockers held
          _ -> []
        remove blocker = Map.update
          (\waiting -> case Set.delete nodeId waiting of
            remaining | Set.null remaining -> Nothing
            remaining -> Just remaining)
          blocker

    wakeResolved environment machine =
      (foldr wake cleared nodeIds, nodeIds)
      where
        nodeIds = Set.toAscList (Set.unions
          [ waiting
          | (blocker, waiting) <- Map.toList (machineBlocked machine)
          , stackBlockerResolved operations environment blocker
          ])
        cleared = foldr unregisterNode machine nodeIds
        wake nodeId = updateNode nodeId (\node -> case rewriteNodeState node of
          NodeHeld held -> node
            { rewriteNodeEnvironment = environment
            , rewriteNodeState = NodeReady (DecideCandidate held)
            }
          _ -> node)

    listAt selected = listHead . drop selected
    listHead [] = Nothing
    listHead (selected : _) = Just selected

    replaceNodeEnvironment nodeId selected = updateNode nodeId (\node -> node
      { rewriteNodeEnvironment = selected })
