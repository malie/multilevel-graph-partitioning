{-# LANGUAGE ScopedTypeVariables , BangPatterns , ParallelListComp #-}
module Data.Graph.Partitioning
       ()
       where

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Vector as V
import qualified System.Random as R

import Data.Ord ( comparing )

import Control.Monad ( replicateM , liftM , when , foldM )

import System.Process ( system )


data Node n
         = Node n
         | CoarseNode Int
         deriving (Eq, Ord, Show)

data Edge e
         = Edge e
         | CoarseEdge Int
         deriving (Eq, Ord, Show)

data Graph n e =
  Graph { nodeEdges :: M.Map (Node n) (S.Set (Edge e))
        , edgeNodes :: M.Map (Edge e) (Node n, Node n)
        , nodeWeight :: M.Map (Node n) Double
        , edgeWeight :: M.Map (Edge e) Double 
        , numNodes :: Int
        , numEdges :: Int 
        , nextId :: Int } 
  deriving (Show)

empty :: Graph n e
empty =
  Graph M.empty M.empty M.empty M.empty 0 0 1

fromList :: (Ord n) => [(n,n)] -> Graph n Int
fromList edges = Graph { nodeEdges =
                            M.unionsWith S.union [ M.fromList [(a, eset), (b,eset)]
                                                 | (e, (a,b)) <- es
                                                 , let eset = S.singleton e ]
                       , edgeNodes = M.fromList es
                       , nodeWeight = nws
                       , edgeWeight = M.fromList [ (e, 1) | (e, _) <- es ]
                       , numNodes = M.size nws
                       , numEdges = length edges
                       , nextId = 1 }
  where es = [ (Edge e, (Node a, Node b))
             | e <- [1..] 
             | (a,b) <- edges ]
        nws = M.fromList $ concat [ [(a, 1), (b,1)] | (_, (a,b)) <- es ]

hasNode :: (Ord n) => Node n -> Graph n e -> Bool
hasNode n g = M.member n (nodeWeight g)

hasEdge :: (Ord e) => Edge e -> Graph n e -> Bool
hasEdge e g = M.member e (edgeWeight g)

addNode :: (Ord n) => Node n -> Graph n e -> Graph n e
addNode n g = addNodeWithWeight n 1.0 g

addNodeWithWeight :: (Ord n) => Node n -> Double -> Graph n e -> Graph n e
addNodeWithWeight n w g 
  | hasNode n g = error "node exists already"
  | otherwise =
    g { nodeEdges = M.insert n S.empty (nodeEdges g)
      , nodeWeight = M.insert n w (nodeWeight g)
      , numNodes = succ (numNodes g) }
                          
addEdge :: (Ord e, Ord n) => Edge e -> Node n -> Node n -> Graph n e -> Graph n e
addEdge e a b g = addEdgeWithWeight e a b 1.0 g

addEdgeWithWeight :: (Ord e, Ord n) => 
                     Edge e -> Node n -> Node n -> Double -> Graph n e -> Graph n e
addEdgeWithWeight e a b w g
  | hasEdge e g = error "edge exists already"
  | not (hasNode a g) = error "node non-existant"
  | not (hasNode b g) = error "node non-existant"
  | otherwise =
    g { nodeEdges = M.update inse a $ M.update inse b (nodeEdges g)
      , edgeNodes = M.insert e (a,b) (edgeNodes g)
      , edgeWeight = M.insert e w (edgeWeight g)
      , numEdges = succ (numEdges g) }
  where inse edges = Just $ S.insert e edges

randomInt :: Int -> Int -> IO Int
randomInt lower upper = R.getStdRandom $ R.randomR (lower, upper)

randomInts :: Int -> Int -> Int -> IO [Int]
randomInts count lower upper = replicateM count (randomInt lower upper)

randomVectorElement :: V.Vector a -> IO a
randomVectorElement v = liftM (v V.!) $ randomInt 0 (pred $ V.length v)

randomDouble :: Double -> Double -> IO Double
randomDouble lower upper = R.getStdRandom $ R.randomR (lower, upper)


-- optimisation: multiple passes to use M.fromAscList and M.unions instead of M.fromList (??)

type EdgeSubset n e = M.Map (Edge e) (Node n, Node n)

randomSetOfEdgesNonOverlapping :: (Ord e, Ord n) => Graph n e -> IO (EdgeSubset n e)
randomSetOfEdgesNonOverlapping g =
  do let n = numEdges g
     is <- randomInts n 0 (pred n)
     es <- rec S.empty is
     return $ M.fromList es
  where edgesVector = V.fromList $ M.toList $ edgeNodes g
        rec _ [] = return []
        rec !seen (!i:is) =
          do let ed@(_, (a, b)) = edgesVector V.! i
             if S.member a seen || S.member b seen
               then rec seen is
               else do rest <- rec (S.insert b (S.insert a seen)) is
                       return $ ed : rest
               
coarsenGraph :: (Ord n, Ord e) => Graph n e -> EdgeSubset n e -> Graph n e
coarsenGraph g es = L.foldl' coarsen g xes
  where 
     xes = [ (CoarseNode xid, ed)
           | xid <- [nextId g..]
           | ed@(e, (a,b)) <- M.toList es ]
     nnextId = case last xes of (CoarseNode x,_) -> x
     coarsen g (nn, (e, (a,b))) =
          Graph { nodeEdges = 
                     updateNodeEdges $ 
                     M.insert nn (edab S.\\ dropEdges) neab
                , edgeNodes = updateEdgeNodes ende
                , nodeWeight = let aw = nodeWeight g M.! a
                                   bw = nodeWeight g M.! b
                               in M.insert nn (aw+bw) $
                                  M.delete a $
                                  M.delete b $ nodeWeight g
                , edgeWeight = updateEdgeWeights $
                               M.delete e $ 
                               edgeWeight g
                , numNodes = numNodes g - 1
                , numEdges = numEdges g - 1 - S.size dropEdges
                , nextId = nnextId }
          where neab = M.delete a $ M.delete b $ nodeEdges g
                ende = M.delete e $ edgeNodes g
                eda =  e `S.delete` (nodeEdges g M.! a)
                edb = e `S.delete` (nodeEdges g M.! b)
                edab = S.union eda edb
                -- reachable nodes
                ra = br eda -- :: S.Set (Node n)
                rb = br edb -- :: S.Set (Node n)
                br edx = S.fromList
                         [ if a == c || b == c then d else c
                         | e <- S.toList edx
                         , let (c,d) = edgeNodes g M.! e ]
                reachableFromBoth = S.intersection ra rb
                dropEdges = S.fromList
                            [ ev
                            | ev <- S.toList edab
                            , let (va,vb) = ende M.! ev
                            , let wr = S.member va reachableFromBoth
                                  vr = S.member vb reachableFromBoth
                            , wr || vr
                            , a == va || a == vb ]
                updateNodeEdges ne = S.foldl' rr ne (S.union ra rb)
                  where rr ne ed =
                          M.adjust (S.\\ dropEdges) ed ne
                updateEdgeNodes en = 
                  let rec en edge =
                        let (c, d) = en M.! edge
                            other = if c == a || c == b
                                    then d
                                    else c
                            rfb = S.member other reachableFromBoth
                        in if rfb
                           then if a == d || a == c
                                then -- drop one
                                  M.delete edge en
                                else -- keep the other
                                  M.insert edge (adj (c,d)) en
                           else
                             M.adjust adj edge en
                      adj (c, d) = 
                        ( if c == a || c == b then nn else c
                        , if d == a || d == b then nn else d)
                  in S.foldl' rec en edab
                updateEdgeWeights ew =
                  let o = M.fromList
                          [ (k, edgeWeight g M.! ea)
                          | ea <- S.toList eda
                          , let (kl, kr) = edgeNodes g M.! ea
                          , let k = if kl == a || kl == b
                                    then kr
                                    else kl
                          , S.member k rb ]
                  in 
                   flip (L.foldl' (\m de -> M.delete de m))
                   (S.toList dropEdges) $
                   L.foldl' (\m (e,w) -> M.insert e w m) ew 
                          [ (eb, eaw+ebw)
                          | eb <- S.toList edb
                          , let (kl, kr) = edgeNodes g M.! eb
                          , let k = if kl == a || kl == b
                                    then kr
                                    else kl
                          , S.member k ra
                          , let ebw = edgeWeight g M.! eb 
                          , let eaw = o M.! k ] 


type Clusters n = M.Map (Node n) Int


partition :: (Ord e, Ord n, Show e, Show n
             , PartitioningGoal pg) =>
             Graph n e -> Int -> pg -> IO (Clusters n)
partition g numClusters pg
  | numNodes g < 3*numClusters = -- magic number '3' ...
    partitionSlow g numClusters pg
  | otherwise =
  do es <- randomSetOfEdgesNonOverlapping g
     putStrLn "coarsening edges:"
     mapM_ print $ M.toList es
     let cg = coarsenGraph g es
     printGraph cg
     cp <- partition cg numClusters pg
     return undefined
  

nodeNeighbours :: (Ord e, Ord n) => Graph n e -> Node n -> [Node n]
nodeNeighbours g n =
  [ neigbour
  | e <- S.toList $ nodeEdges g M.! n
  , neigbour <- tupleToList $ edgeNodes g M.! e
  , neigbour /= n ]

tupleToList :: (a,a) -> [a]
tupleToList (a,b) = [a,b]
  


data Score = Score { cutEdges :: Double 
                   , imbalance :: Double 
                   , clusterWeights :: M.Map Int Double 
                   , targetWeight :: Double }

instance Show Score where
  show (Score ce ib _ _) = "(ce:" ++ show ce ++ " ib:" ++ show ib ++ ")"

class PartitioningGoal a where
  scoreAssignment :: (Ord e, Ord n) =>
                     a -> Graph n e -> Clusters n -> Score
  scoreChange :: (Ord e, Ord n) =>
                 a -> Graph n e -> Clusters n -> Node n -> Int
                 -> Score -> Score
  compareScores :: a -> Score -> Score -> Ordering
    

data MinimalCuts = MinimalCuts

instance PartitioningGoal MinimalCuts where
  scoreAssignment _ g cl = Score ce ib weights avg
    where 
      ce = sum [ edgeWeight g M.! e
               | (e, (a, b)) <- M.toList $ edgeNodes g
               , cl M.! a /= cl M.! b ]
      ib = sum [ (x - avg) ** 2 | x <- sizes ]
      sizes = map snd $ M.toList $ 
              M.fromListWith (+)
              [ (x, nodeWeight g M.! node)
              | (node, x) <- M.toList cl ]
      avg = sum sizes / fromIntegral (length sizes)
      weights = M.fromListWith (+) [ (cluster, nodeWeight g M.! n) 
                                   | (n, cluster) <- M.toList cl ]
  -- how does the score change if 'node' is in cluster 'newCluster'?
  scoreChange _ g clustering node newCluster (Score ce0 ib0 weights1 targetWeight) =
    Score (ce0 
           - scoreEdges nedges clustering
           + scoreEdges nedges newclustering)
          (ib0 - clweight weights1 oldCluster - clweight weights1 newCluster
               + clweight weights2 oldCluster + clweight weights2 newCluster)
          weights2
          targetWeight
    where
      oldCluster = clustering M.! node
      newclustering = M.insert node newCluster clustering
      nedges = S.toList $ nodeEdges g M.! node
      scoreEdges es as = sum $ map sc es
          where sc e = let (a,b) = edgeNodes g M.! e
                       in if as M.! a == as M.! b
                          then 0.0
                          else edgeWeight g M.! e
      nw = nodeWeight g M.! node :: Double
      weights2 = M.adjust (+nw) newCluster $
                 M.adjust (subtract nw) oldCluster weights1
      clweight ws c = ((ws M.! c) - targetWeight) ** 2
  compareScores _ (Score cex ibx _ _) (Score cey iby _ _) =
    case (compare cex cey, compare ibx iby) of
      (GT, _)  -> GT
      --(LT, GT) -> EQ -- ???
      (_, GT) -> GT
      (EQ, EQ) -> EQ
      (_, _)   -> LT


data BalancedClusters = BalancedClusters

instance PartitioningGoal BalancedClusters where
  scoreAssignment _ g cl = undefined
  scoreChange _ g cl node newcluster sc = undefined
  compareScores _ a b = undefined


-- | a random clustering to start up 'partitionSlow'
randomAssignment :: (Ord n, Ord e, Show n) =>
                    Graph n e -> Int -> IO (Clusters n)
randomAssignment g numClusters =
  do let es = V.fromList $ M.keys $ nodeEdges g
     let len = V.length es
     is0 <- randomInts len 0 (pred len)
     let is = L.nub is0
     grow $ M.fromList $ concat $
       [ [(n, cl) ]
       | cl <- [1 .. numClusters]
       | i <- is
       , let n = es V.! i]
  where grow as =
          do let m = concat
                     [ if M.member a as && M.notMember b as
                       then [(b, as M.! a)]
                       else if M.member b as && M.notMember a as
                            then [(a, as M.! b)]
                            else []
                     | (a,b) <- M.elems $ edgeNodes g ]
             if null m
               then return as
               else grow $ M.union as $ M.fromList m
-- maybe randomAssignment should first assign those nodes
-- with largest weight, then extend via edges with largest weights



-- | refine random cluster assignments by "local search".
partitionSlow :: (Ord e, Ord n, Show e, Show n,
                  PartitioningGoal pg) =>
                 Graph n e -> Int -> pg -> IO (Clusters n)
partitionSlow g numClusters pg =
  do as <- randomAssignment g numClusters
     mapM_ print $ M.toList as
     let score0 = scoreAssignment pg g as
     print score0
     (nas, score1) <- localSearch (5*numNodes g) as score0
     print score1
     putStr "recalculated: "
     let score2 = scoreAssignment pg g nas
     print score2
     return nas
  where nodes = V.fromList $ M.keys $ nodeWeight g
        randomNode = randomVectorElement nodes
        localSearch 0 as sc = return (as, sc)
        localSearch i as sc1 =
          do n <- randomNode
             let neighbours = nodeNeighbours g n
                 nclusters = S.fromList $ map (as M.!) neighbours
                 options =
                   [ (scoreChange pg g as n ncl sc1, as2)
                   | ncl <- S.toList nclusters
                   , let as2 = M.insert n ncl as
                   -- avoid dropping last in cluster
                   , S.size (S.fromList $ M.elems as2)
                     == numClusters ]
             if null options
               then localSearch (pred i) as sc1
               else ls i as n sc1 options
        ls i as n sc1 options =
          do mapM_ (\(sc, as)-> print(i, n, as M.! n, sc)) options
             let cp a b = compareScores pg (fst a) (fst b)
                 (bestSc, bestAs) = L.minimumBy cp options
             when (compareScores pg sc1 bestSc == GT) $
               putStrLn (show i ++ " improved "
                         ++ show sc1 ++ " to " ++ show bestSc
                         ++ " by assigning " ++ show (bestAs M.! n)
                         ++ " to " ++ show n)

             localSearch (pred i) bestAs bestSc

-- actually all that partitioning stuff can
-- be restarted at any level



printGraph :: (Show n, Show e) => Graph n e -> IO ()
printGraph g =
  do putStrLn "Graph\n  nodeEdges:"
     mapM_ printi $ M.toList $ nodeEdges g
     putStrLn "  edgeNodes:"
     mapM_ printi $ M.toList $ edgeNodes g
     putStrLn "  nodeWeight:"
     mapM_ printi $ M.toList $ nodeWeight g
     putStrLn "  edgeWeight:"
     mapM_ printi $ M.toList $ edgeWeight g
     putStrLn $ "  numNodes: " ++ show (numNodes g) 
       ++ "  numEdges: " ++ show (numEdges g)
       ++ "  nextId: " ++ show (nextId g)
  where printi x =
          do putStr "    "
             print x
     
  
  
testGraph1 :: Graph Int Int
testGraph1 =
  fromList [(100,200), (200, 300), (300,400), 
            (100,150), (150, 200),
            (100,160), (200, 160) ]

testGraph2 :: Graph Int Int
testGraph2 =
  fromList [(100,200), (100, 110), (110,200), 
            (200,300), (200, 210), (210,220), (220, 300),
            (300,400), (300,310), (310,400),
            (400,410), (400, 500), (410,500),
            (500,600), 
            (600, 610), 
            (600, 100), (610,100)]

type ExampleGraph3 = Graph (Int,Int,Int) Int

randomGraphFromRectangles :: Int -> Int -> Int -> Int
                       -> IO ExampleGraph3
randomGraphFromRectangles numRects width height numConnections =
  do g <- rectangleNodes 0 empty
     let es = rectangleEdges 0
     ees <- replicateM numConnections extraEdge
     foldM ae g (zip [1..] (es ++ ees))
  where rectangleNodes :: Int -> ExampleGraph3 -> IO ExampleGraph3
        rectangleNodes n g
          | n == numRects = return g
          | otherwise =
            do g2 <- foldM (an n) g
                     [ (x,y)
                     | x <- [1..width]
                     , y <- [1..height]]
               rectangleNodes (succ n) g2
        an n g (x,y) =
          do w <- randomWeight
             return $ addNodeWithWeight (Node (n,x,y)) w g
        randomWeight =
          do r <- randomDouble 1.0 10.0
             return $ fromIntegral (round $ r*10) / 10
        rectangleEdges n
          | n == numRects = []
          | otherwise =
            [ ((n,u,v), (n,x,y))
                 | u <- [1..width]
                 , v <- [1..height]
                 , (x,y) <- [(u+1, v), (u, v+1)]
                 , x <= width
                 , y <= height ]
            ++ rectangleEdges (succ n) 
        extraEdge =
          do rect1 <- randomInt 0 (pred numRects)
             u <- randomInt 1 width
             v <- randomInt 1 height
             rect2 <- randomInt 0 (pred numRects)
             x <- randomInt 1 width
             y <- randomInt 1 height
             return ((rect1, u, v), (rect2, x, y))
        ae g (egdeId, ((r,u,v),(rr,x,y))) =
          do w <- randomWeight
             return $ addEdgeWithWeight (Edge egdeId)
               (Node (r,u,v)) (Node (rr,x,y)) w g





-- | write a dot file
writeDotFile :: (Show n) =>
                String -> Graph n e -> Maybe (Clusters n) -> IO ()
writeDotFile filename g maybeClusters =
  writeFile filename $ concat $
  [ "graph aGraph {\n"
  , "  edge[len=1.6]" ]
  ++ (case maybeClusters of
         Nothing -> []
         Just clusters ->
           [ "  " ++ sq n
             ++ "[style=filled, color=\"/"
             ++ colorscheme ++ "/" ++ show (c+1) ++ "\"];\n"
           | (n,c) <- M.toList clusters ])
  ++ [ "  " ++ sq a ++ " -- " ++ sq b ++ ";\n"
     | (a,b) <- M.elems $ edgeNodes g ]
  ++ [ "}\n"]
  where sq n = "\"" ++ show n ++ "\""
        colorscheme = "rdylgn10"

showGraph :: (Show n) => Graph n e -> Maybe (Clusters n) -> IO ()
showGraph g cl =
  do writeDotFile "last.gv" g cl
     system "neato -Tsvg last.gv > last.svg"
     system "emacsclient -n last.svg"
     return ()

