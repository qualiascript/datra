module SyntaxRewriting.Stack
  ( RewriteStackOperations (..)
  , runRewriteStack
  ) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.List.NonEmpty (NonEmpty (..))
import Control.Monad.Trans.State.Strict (State, runState, state)
import SyntaxRewriting.Dependencies
  ( DependencyGraph
  , emptyDependencyGraph
  , registerDependencies
  , releaseDependency
  )
import SyntaxRewriting.Types
  ( CandidateAttempt (..)
  , CandidateContinuation (..)
  , CandidateFrame (..)
  , CandidateFrameProgress (..)
  , CandidateRejection
  , CandidateRejectionDetails
  , CandidateTypingContext
  , RewriteDependency (RewriteNodeResult, SequenceDeclarations)
  , RewriteNode (..)
  , RewriteNodeId (..)
  , RewriteNodeState (..)
  , RewriteParent (..)
  , RewriteResult (..)
  , PreparedExpansion (..)
  , SequenceFrame (..)
  , SequenceId (..)
  , RewriteTask (..)
  , StructuralCandidate (..)
  , SelectedCandidate (..)
  )
import DatraLanguage.AST
  ( Expression (..), traverseExpressionChildren )
import DatraLanguage.SyntaxTemplate
  ( SyntaxHoleKind
  , TemplateSelection (..)
  )
import DatraTypes (InterpretedValue, SyntaxFunctionExpansion (..))
import SyntaxRewriting.Candidates
  ( advanceCandidateFrameWith
  , candidateFrameRequiresTypedChild
  , initialCandidateFrame
  )

data RewriteStackOperations environment failure = RewriteStackOperations
  { stackEnumerateCandidates
      :: Bool
      -> environment
      -> Expression
      -> [StructuralCandidate]
  , stackCaptureHole
      :: environment
      -> StructuralCandidate
      -> [(SyntaxHoleKind Expression, Expression)]
      -> SyntaxHoleKind Expression
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
      :: InterpretedValue
      -> InterpretedValue
      -> Bool
  , stackOrdinaryChild
      :: environment
      -> Expression
      -> Int
      -> Maybe (environment, Expression)
  , stackFinalizeOrdinary
      :: environment
      -> Expression
      -> Either failure RewriteResult
  , stackAssembleSequence
      :: environment
      -> Expression
      -> [Expression]
      -> Either failure Expression
  , stackAssembleExpansion
      :: environment
      -> SyntaxFunctionExpansion
      -> [Expression]
      -> Either failure Expression
  , stackSequenceEntries
      :: environment
      -> Expression
      -> Maybe (environment, environment, [Expression])
  , stackPublishDeclaration
      :: environment
      -> environment
      -> [Expression]
      -> [(Int, RewriteResult)]
      -> Int
      -> RewriteResult
      -> Either failure (Maybe environment)
  , stackPrepareCandidate
      :: environment
      -> SelectedCandidate
      -> PreparedExpansion
  , stackExpansionWork
      :: environment
      -> PreparedExpansion
      -> Either Expression (environment, environment, [Expression])
  , stackCandidateRejection
      :: environment
      -> CandidateRejectionDetails
      -> [CandidateRejection]
      -> CandidateRejection
  }

data RewriteMachine environment = RewriteMachine
  { machineNodes :: Map RewriteNodeId (RewriteNode environment)
  , machineSequences
      :: Map SequenceId (SequenceFrame environment)
  , machineDependencies :: DependencyGraph
  , machineNextNode :: Int
  , machineNextSequence :: Int
  }

emptyRewriteMachine :: RewriteMachine environment
emptyRewriteMachine = RewriteMachine
  { machineNodes = Map.empty
  , machineSequences = Map.empty
  , machineDependencies = emptyDependencyGraph
  , machineNextNode = 0
  , machineNextSequence = 0
  }

allocateRewriteNode
  :: environment
  -> Expression
  -> RewriteParent
  -> RewriteMachine environment
  -> (RewriteNodeId, RewriteMachine environment)
allocateRewriteNode environment source parent machine =
  (nodeId, machine
    { machineNodes = Map.insert nodeId node (machineNodes machine)
    , machineNextNode = machineNextNode machine + 1
    })
  where
    nodeId = RewriteNodeId (machineNextNode machine)
    node = RewriteNode
      { rewriteNodeId = nodeId
      , rewriteNodeSource = source
      , rewriteNodeEnvironment = environment
      , rewriteNodeCandidates = []
      , rewriteNodeAttempts = []
      , rewriteNodeCandidateCursor = 0
      , rewriteNodeParent = parent
      , rewriteNodeExpression = source
      , rewriteNodeOrdinaryCursor = 0
      , rewriteNodeOrdinaryChild = Nothing
      , rewriteNodeOrdinaryResult = Nothing
      , rewriteNodeState = NodePending
      }

rewriteNodeAt
  :: RewriteNodeId
  -> RewriteMachine environment
  -> RewriteNode environment
rewriteNodeAt nodeId = (Map.! nodeId) . machineNodes

updateRewriteNode
  :: RewriteNodeId
  -> (RewriteNode environment -> RewriteNode environment)
  -> RewriteMachine environment
  -> RewriteMachine environment
updateRewriteNode nodeId update machine = machine
  { machineNodes = Map.adjust update nodeId (machineNodes machine) }

sequenceFrameAt
  :: SequenceId
  -> RewriteMachine environment
  -> SequenceFrame environment
sequenceFrameAt sequenceId = (Map.! sequenceId) . machineSequences

updateSequenceFrame
  :: SequenceId
  -> (SequenceFrame environment -> SequenceFrame environment)
  -> RewriteMachine environment
  -> RewriteMachine environment
updateSequenceFrame sequenceId update machine = machine
  { machineSequences = Map.adjust update sequenceId
      (machineSequences machine) }

allocateSequenceFrame
  :: RewriteNodeId
  -> Expression
  -> environment
  -> environment
  -> [Expression]
  -> Maybe (SelectedCandidate, PreparedExpansion)
  -> RewriteMachine environment
  -> (SequenceId, RewriteMachine environment)
allocateSequenceFrame owner source initialEnvironment environment
    entries expansion machine =
  (sequenceId, allocated
    { machineSequences = Map.insert sequenceId frame
        (machineSequences allocated)
    , machineNextSequence = machineNextSequence machine + 1
    })
  where
    sequenceId = SequenceId (machineNextSequence machine)
    (nodes, allocated) =
      foldl allocate ([], machine) entries
    allocate (nodeIds, current) entry =
      let (nodeId, next) = allocateRewriteNode environment entry
            (RewriteSequenceParent sequenceId) current
      in (nodeIds <> [nodeId], next)
    frame = SequenceFrame
      { sequenceFrameId = sequenceId
      , sequenceFrameOwner = owner
      , sequenceFrameSource = source
      , sequenceFrameNodes = nodes
      , sequenceFrameInitialEnvironment = initialEnvironment
      , sequenceFrameEnvironment = environment
      , sequenceFrameCursor = 0
      , sequenceFrameResults = Map.empty
      , sequenceFrameDeclarationsComplete = False
      , sequenceFrameExpansion = expansion
      }

blockRewriteNode
  :: RewriteNodeId
  -> Set RewriteDependency
  -> RewriteMachine environment
  -> RewriteMachine environment
blockRewriteNode nodeId dependencies machine =
  (updateRewriteNode nodeId
    (\node -> node { rewriteNodeState = NodeWaiting dependencies })
    machine)
      { machineDependencies = registerDependencies nodeId dependencies
          (machineDependencies machine) }

finalizeRewriteNode
  :: RewriteNodeId
  -> RewriteResult
  -> RewriteMachine environment
  -> RewriteMachine environment
finalizeRewriteNode nodeId result machine =
  finalized { machineDependencies = remainingDependencies }
  where
    finalized = updateRewriteNode nodeId
      (\node -> node { rewriteNodeState = NodeFinalized result })
      machine
    (_, remainingDependencies) = releaseDependency
      (RewriteNodeResult nodeId) (machineDependencies machine)

replaceExpressionChild :: Int -> Expression -> Expression -> Expression
replaceExpressionChild selected replacement source = fst
  (runState (traverseExpressionChildren replace source) 0)
  where
    replace :: Expression -> State Int Expression
    replace child = state $ \index ->
      (if index == selected then replacement else child, index + 1)

materializeSequence
  :: RewriteStackOperations environment failure
  -> environment
  -> Expression
  -> [RewriteResult]
  -> Either failure RewriteResult
materializeSequence operations environment source results = do
  expressionValue <- stackAssembleSequence operations
    environment source expressions
  stackFinalizeOrdinary operations environment expressionValue
  where
    expressions = map rewriteResultExpression results

materializeExpansion
  :: RewriteStackOperations environment failure
  -> environment
  -> PreparedExpansion
  -> [RewriteResult]
  -> Either failure Expression
materializeExpansion operations environment prepared results = do
  core <- stackAssembleExpansion operations environment
    (preparedExpansionSyntax prepared) expressions
  pure (foldl FunctionApplication core
    (preparedExpansionRemaining prepared))
  where
    expressions = map rewriteResultExpression results

-- | Execute one rewrite choice point with an explicit task stack. A root
-- finalization is the terminal scheduler transition; execution never drains
-- the stack and then guesses whether rewriting completed.
runRewriteStack
  :: RewriteStackOperations environment failure
  -> environment
  -> Expression
  -> Either failure (RewriteResult, [CandidateRejection])
runRewriteStack operations environment source =
  executeTask (EnterNode root) [] allocated
  where
    (root, allocated) = allocateRewriteNode
      environment source RewriteRoot emptyRewriteMachine

    executeTask task backlog machine = step task backlog machine

    continueTasks (next :| scheduled) backlog machine =
      executeTask next (scheduled <> backlog) machine

    finishNode node result backlog machine =
      let nodeId = rewriteNodeId node
          finalized = finalizeRewriteNode nodeId result machine
          rejections = rejectedAttempts (rewriteNodeAttempts node)
      in case rewriteNodeParent node of
        RewriteRoot -> Right (result, rejections)
        RewriteCandidateParent continuation ->
          continueTasks
            (ResumeCandidate
              (continuationParentNode continuation)
              (continuationCandidateCursor continuation) :| [])
            backlog finalized
        RewriteOrdinaryParent parent ->
          continueTasks (ResumeOrdinary parent :| []) backlog finalized
        RewriteSequenceParent sequenceId ->
          continueTasks (ResumeSequence sequenceId nodeId :| [])
            backlog finalized

    step task backlog machine = case task of
      EnterNode nodeId ->
        let node = rewriteNodeAt nodeId machine
            candidateSource = rewriteNodeExpression node
            candidates = stackEnumerateCandidates operations
              (case rewriteNodeParent node of RewriteRoot -> True; _ -> False)
              (rewriteNodeEnvironment node) candidateSource
            entered = updateRewriteNode nodeId
              (\current -> current
                { rewriteNodeCandidates = candidates
                , rewriteNodeState = NodeActive
                , rewriteNodeCandidateCursor = 0
                }) machine
            active = rewriteNodeAt nodeId entered
        in if null candidates
            then beginOrdinary active backlog entered
            else continueTasks (TryCandidate nodeId 0 :| []) backlog entered
      TryCandidate nodeId cursor ->
        continueCandidate nodeId cursor Nothing backlog machine
      ResumeCandidate nodeId cursor ->
        continueCandidate nodeId cursor
          (activeFrame nodeId cursor machine) backlog machine
      ResumeOrdinary nodeId ->
        advanceOrdinary (rewriteNodeAt nodeId machine) backlog machine
      EnterSequence sequenceId ->
        enterSequence (sequenceFrameAt sequenceId machine) backlog machine
      ResumeSequence sequenceId childId ->
        resumeSequence (sequenceFrameAt sequenceId machine)
          childId backlog machine
      ResumeSequenceDeclarations sequenceId nodeId ->
        resumeSequenceDeclarations
          (sequenceFrameAt sequenceId machine) nodeId backlog machine
      FinalizeSequence sequenceId ->
        finalizeSequence (sequenceFrameAt sequenceId machine) backlog machine

    continueCandidate nodeId cursor stored backlog machine =
      let node = rewriteNodeAt nodeId machine
      in case drop cursor (rewriteNodeCandidates node) of
          [] -> beginOrdinary node backlog machine
          candidate : _ ->
            let frame = maybe (initialCandidateFrame candidate) id stored
                nodeEnvironment = rewriteNodeEnvironment node
                progress = advanceCandidateFrameWith
                  (stackCaptureHole operations nodeEnvironment candidate)
                  (stackExpectedHole operations nodeEnvironment candidate)
                  (stackCandidateReturn operations nodeEnvironment candidate)
                  (finalizedResult machine)
                  (stackTypesCompatible operations)
                  frame
            in handleProgress node cursor frame progress backlog machine

    handleProgress node cursor frame progress backlog machine =
      case progress of
        CandidateFrameNeedsChild index _ sourceExpression ->
          let parentId = rewriteNodeId node
              continuation = CandidateContinuation parentId cursor index
              childEnvironment = rewriteNodeEnvironment node
              (childId, allocatedChild) = allocateRewriteNode
                childEnvironment sourceExpression
                (RewriteCandidateParent continuation)
                machine
              continuedFrame = frame
                { candidateFrameChildren = Map.insert index childId
                    (candidateFrameChildren frame) }
              dependency = RewriteNodeResult childId
              blocked = setCurrentAttempt parentId cursor
                (CandidateBlocked
                  (candidateFrameCandidate frame)
                  continuedFrame
                  (Set.singleton dependency)) allocatedChild
              waiting = blockRewriteNode parentId
                (Set.singleton dependency) blocked
          in continueTasks (EnterNode childId :| []) backlog waiting
        CandidateFrameBlocked dependencies ->
          let nodeId = rewriteNodeId node
              blocked = setCurrentAttempt nodeId cursor
                (CandidateBlocked
                  (candidateFrameCandidate frame) frame dependencies) machine
              waiting = blockRewriteNode nodeId dependencies blocked
              dependencyTasks = map dependencyTask (Set.toAscList dependencies)
          in case dependencyTasks of
            next : remaining -> continueTasks (next :| remaining)
              backlog waiting
            [] -> continueTasks (ResumeCandidate nodeId cursor :| [])
              backlog waiting
        CandidateFrameRejected details ->
          let nodeId = rewriteNodeId node
              rejection = stackCandidateRejection operations
                (rewriteNodeEnvironment node) details
                (frameRejections frame machine)
              rejected = setCurrentAttempt nodeId cursor
                (CandidateRejected rejection) machine
              next = cursor + 1
              advanced = updateRewriteNode nodeId
                (\current -> current
                  { rewriteNodeCandidateCursor = next
                  , rewriteNodeState = NodeActive
                  }) rejected
          in continueTasks (TryCandidate nodeId next :| []) backlog advanced
        CandidateFrameAccepted _ childResults returnType -> do
          let candidate = candidateFrameCandidate frame
              rewrittenCaptures = map rewriteResultExpression childResults
              selection = (structuralCandidateSelection candidate)
                { templateSelectionCaptures = rewrittenCaptures }
              selected = SelectedCandidate
                { selectedStructuralCandidate = candidate
                , selectedCaptures = childResults
                , selectedReturnType = returnType
                }
              selectedCandidate = selected
                { selectedStructuralCandidate = candidate
                    { structuralCandidateSelection = selection } }
              selectedEnvironment = rewriteNodeEnvironment node
              expansion = stackPrepareCandidate operations
                selectedEnvironment selectedCandidate
              nodeId = rewriteNodeId node
          case stackExpansionWork operations
              selectedEnvironment expansion of
            Left expanded ->
              finishCandidate node cursor selectedCandidate expanded
                backlog machine
            Right (initialEnvironment, sequenceEnvironment, entries) ->
              let sourceExpression = AtlasMap entries
                  (sequenceId, withSequence) = allocateSequenceFrame
                    nodeId sourceExpression initialEnvironment
                    sequenceEnvironment entries
                    (Just (selectedCandidate, expansion)) machine
                  active = updateRewriteNode nodeId
                    (\current -> current { rewriteNodeState = NodeActive })
                    withSequence
              in continueTasks (EnterSequence sequenceId :| []) backlog active

    finishCandidate node cursor selected expanded backlog machine =
      let result = RewriteResult expanded (Just (selectedReturnType selected))
            (Just selected)
          nodeId = rewriteNodeId node
          accepted = setCurrentAttempt nodeId cursor
            (CandidateAccepted selected) machine
      in finishNode (rewriteNodeAt nodeId accepted) result backlog accepted

    beginOrdinary node backlog machine =
      case rewriteNodeOrdinaryResult node of
        Just result -> finishOrdinary node result backlog machine
        Nothing -> case stackSequenceEntries operations
            (rewriteNodeEnvironment node) (rewriteNodeSource node) of
          Just (initialEnvironment, sequenceEnvironment, entries) ->
            let owner = rewriteNodeId node
                sourceExpression = rewriteNodeSource node
                (sequenceId, withSequence) = allocateSequenceFrame
                  owner sourceExpression initialEnvironment
                  sequenceEnvironment entries Nothing machine
                active = updateRewriteNode owner
                  (\current -> current { rewriteNodeState = NodeActive })
                  withSequence
            in continueTasks (EnterSequence sequenceId :| []) backlog active
          Nothing -> advanceOrdinary node backlog machine

    finishOrdinary node result backlog machine =
      case sequenceDependencyFor node result machine of
        Nothing -> finishNode node result backlog machine
        Just sequenceId ->
          let nodeId = rewriteNodeId node
              dependency = SequenceDeclarations sequenceId
              stored = updateRewriteNode nodeId
                (\current -> current
                  { rewriteNodeOrdinaryResult = Just result }) machine
              waiting = blockRewriteNode nodeId
                (Set.singleton dependency) stored
          in continueTasks (EnterSequence sequenceId :| []) backlog waiting

    enterSequence frame backlog machine =
      case drop (sequenceFrameCursor frame) (sequenceFrameNodes frame) of
        []
          | Map.size (sequenceFrameResults frame) ==
              length (sequenceFrameNodes frame) ->
              continueTasks
                (FinalizeSequence (sequenceFrameId frame) :| []) backlog machine
          | not (sequenceFrameDeclarationsComplete frame) ->
              let sequenceId = sequenceFrameId frame
                  completedDiscovery = updateSequenceFrame sequenceId
                    (\current -> current
                      { sequenceFrameDeclarationsComplete = True }) machine
                  (releasedNodes, remainingDependencies) = releaseDependency
                    (SequenceDeclarations sequenceId)
                    (machineDependencies completedDiscovery)
                  released = completedDiscovery
                    { machineDependencies = remainingDependencies }
                  tasks = map
                    (ResumeSequenceDeclarations sequenceId)
                    releasedNodes
              in case tasks of
                next : remaining -> continueTasks (next :| remaining)
                  backlog released
                [] -> case unfinishedSequenceTasks frame released of
                  next : remaining -> continueTasks (next :| remaining)
                    backlog released
                  [] -> continueTasks (FinalizeSequence sequenceId :| [])
                    backlog released
          | otherwise ->
              case unfinishedSequenceTasks frame machine of
                next : remaining -> continueTasks (next :| remaining)
                  backlog machine
                [] -> continueTasks (FinalizeSequence
                    (sequenceFrameId frame) :| []) backlog machine
        childId : _ ->
          let childEnvironment = sequenceFrameEnvironment frame
              advanced = updateSequenceFrame (sequenceFrameId frame)
                (\current -> current
                  { sequenceFrameCursor = sequenceFrameCursor current + 1 })
                machine
              prepared = updateRewriteNode childId
                (\current -> current
                  { rewriteNodeEnvironment = childEnvironment
                  , rewriteNodeCandidates = []
                  , rewriteNodeCandidateCursor = 0
                  , rewriteNodeAttempts = []
                  , rewriteNodeState = NodePending
                  }) advanced
          in continueTasks
              (EnterNode childId :| [EnterSequence (sequenceFrameId frame)])
              backlog prepared

    resumeSequence frame childId backlog machine =
      case finalizedResult machine childId of
        Nothing -> continueTasks (EnterNode childId :| []) backlog machine
        Just result -> do
          let position = length (takeWhile (/= childId)
                (sequenceFrameNodes frame))
              earlierResults =
                [ (index, earlier)
                | (index, earlierNode) <- zip [0 :: Int ..]
                    (sequenceFrameNodes frame)
                , index < position
                , Just earlier <- [Map.lookup earlierNode
                    (sequenceFrameResults frame)]
                ]
          publication <- stackPublishDeclaration operations
            (sequenceFrameInitialEnvironment frame)
            (sequenceFrameEnvironment frame)
            [ rewriteNodeSource (rewriteNodeAt nodeId machine)
            | nodeId <- sequenceFrameNodes frame
            ]
            earlierResults position result
          let completed = Map.insert childId result
                (sequenceFrameResults frame)
              nextEnvironment = maybe
                (sequenceFrameEnvironment frame) id publication
              advanced = updateSequenceFrame (sequenceFrameId frame)
                (\current -> current
                  { sequenceFrameEnvironment = nextEnvironment
                  , sequenceFrameResults = completed
                  }) machine
              (waiters, awakened) = case publication of
                Nothing -> ([], advanced)
                Just _ ->
                  let (releasedNodes, releasedGraph) = releaseDependency
                        (SequenceDeclarations (sequenceFrameId frame))
                        (machineDependencies advanced)
                  in (releasedNodes, advanced
                      { machineDependencies = releasedGraph })
              wakeTasks =
                [ ResumeSequenceDeclarations (sequenceFrameId frame) nodeId
                | nodeId <- waiters
                ]
              sequenceComplete = Map.size completed ==
                length (sequenceFrameNodes frame)
              scheduled
                | sequenceComplete =
                    FinalizeSequence (sequenceFrameId frame) : wakeTasks
                | otherwise = wakeTasks <>
                    [EnterSequence (sequenceFrameId frame)]
          case scheduled of
            next : remaining -> continueTasks (next :| remaining)
              backlog awakened
            [] -> continueTasks (EnterSequence
                (sequenceFrameId frame) :| []) backlog awakened

    finalizeSequence frame backlog machine = do
      let results =
            [ result
            | childId <- sequenceFrameNodes frame
            , Just result <- [Map.lookup childId
                (sequenceFrameResults frame)]
            ]
          owner = rewriteNodeAt (sequenceFrameOwner frame) machine
          withoutSequence = machine
            { machineSequences = Map.delete (sequenceFrameId frame)
                (machineSequences machine) }
      case sequenceFrameExpansion frame of
        Nothing -> do
          result <- materializeSequence operations
            (sequenceFrameInitialEnvironment frame)
            (sequenceFrameSource frame) results
          finishNode owner result backlog withoutSequence
        Just (selected, expansion) -> do
          expanded <- materializeExpansion operations
            (sequenceFrameInitialEnvironment frame) expansion
            results
          finishCandidate owner (rewriteNodeCandidateCursor owner)
            selected expanded backlog withoutSequence

    resumeSequenceDeclarations frame nodeId backlog machine =
      let selectedEnvironment = sequenceFrameEnvironment frame
          prepared = updateRewriteNode nodeId
            (\current -> current
              { rewriteNodeEnvironment = selectedEnvironment
              , rewriteNodeCandidates = []
              , rewriteNodeCandidateCursor = 0
              , rewriteNodeAttempts = []
              , rewriteNodeState = NodePending
              }) machine
      in continueTasks (EnterNode nodeId :| []) backlog prepared

    dependencyTask dependency = case dependency of
      RewriteNodeResult nodeId -> EnterNode nodeId
      SequenceDeclarations sequenceId -> EnterSequence sequenceId

    sequenceDependencyFor node result machine
      | Just _ <- rewriteResultType result = Nothing
      | RewriteCandidateParent continuation <- rewriteNodeParent node
      , Just frame <- activeFrame
          (continuationParentNode continuation)
          (continuationCandidateCursor continuation)
          machine
      , candidateFrameRequiresTypedChild frame
      , Just sequenceId <- containingSequence
          (continuationParentNode continuation) machine
      , not (sequenceFrameDeclarationsComplete
          (sequenceFrameAt sequenceId machine)) = Just sequenceId
      | otherwise = Nothing

    containingSequence nodeId machine =
      case rewriteNodeParent (rewriteNodeAt nodeId machine) of
        RewriteRoot -> Nothing
        RewriteSequenceParent sequenceId -> Just sequenceId
        RewriteOrdinaryParent parent -> containingSequence parent machine
        RewriteCandidateParent continuation ->
          containingSequence (continuationParentNode continuation) machine

    unfinishedSequenceTasks frame machine =
      [ task
      | nodeId <- sequenceFrameNodes frame
      , Map.notMember nodeId (sequenceFrameResults frame)
      , let node = rewriteNodeAt nodeId machine
      , task <- case rewriteNodeState node of
          NodePending -> [EnterNode nodeId]
          NodeActive -> [TryCandidate nodeId
            (rewriteNodeCandidateCursor node)]
          NodeWaiting _ -> [ResumeCandidate nodeId
            (rewriteNodeCandidateCursor node)]
          NodeFinalized _ -> [ResumeSequence (sequenceFrameId frame) nodeId]
      ]

    advanceOrdinary node backlog machine =
      case rewriteNodeOrdinaryChild node of
        Just childId -> case finalizedResult machine childId of
          Nothing -> continueTasks (EnterNode childId :| []) backlog machine
          Just childResult ->
            let nodeId = rewriteNodeId node
                cursor = rewriteNodeOrdinaryCursor node
                updatedExpression = replaceExpressionChild cursor
                  (rewriteResultExpression childResult)
                  (rewriteNodeExpression node)
                advanced = updateRewriteNode nodeId
                  (\current -> current
                    { rewriteNodeExpression = updatedExpression
                    , rewriteNodeOrdinaryCursor = cursor + 1
                    , rewriteNodeOrdinaryChild = Nothing
                    }) machine
            in continueTasks (ResumeOrdinary nodeId :| []) backlog advanced
        Nothing ->
          case stackOrdinaryChild operations
              (rewriteNodeEnvironment node)
              (rewriteNodeExpression node)
              (rewriteNodeOrdinaryCursor node) of
            Nothing -> do
              result <- stackFinalizeOrdinary operations
                (rewriteNodeEnvironment node) (rewriteNodeExpression node)
              finishOrdinary node result backlog machine
            Just (childEnvironment, childSource) ->
              let parentId = rewriteNodeId node
                  (childId, allocatedChild) = allocateRewriteNode
                    childEnvironment childSource
                    (RewriteOrdinaryParent parentId)
                    machine
                  dependency = RewriteNodeResult childId
                  prepared = updateRewriteNode parentId
                    (\current -> current
                      { rewriteNodeOrdinaryChild = Just childId })
                    allocatedChild
                  waiting = blockRewriteNode parentId
                    (Set.singleton dependency) prepared
              in continueTasks (EnterNode childId :| []) backlog waiting

    finalizedResult machine nodeId = do
      case rewriteNodeState (rewriteNodeAt nodeId machine) of
        NodeFinalized result -> Just result
        _ -> Nothing

    activeFrame nodeId cursor machine = do
      let node = rewriteNodeAt nodeId machine
      case drop cursor (rewriteNodeAttempts node) of
        CandidateBlocked _ frame _ : _ -> Just frame
        _ -> Nothing

    setCurrentAttempt nodeId cursor attempt = updateRewriteNode nodeId
      (\node -> node
        { rewriteNodeAttempts = replaceAt cursor attempt
            (rewriteNodeAttempts node) })

    replaceAt index value attempts
      | index < length attempts =
          take index attempts <> [value] <> drop (index + 1) attempts
      | otherwise = attempts <> [value]

    rejectedAttempts = foldr collect []
      where
        collect (CandidateRejected rejection) remaining =
          rejection : remaining
        collect _ remaining = remaining

    frameRejections frame machine = concat
      [ rejectedAttempts (rewriteNodeAttempts (rewriteNodeAt child machine))
      | (_, child) <- Map.toAscList (candidateFrameChildren frame)
      ]
