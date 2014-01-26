multilevel-graph-partitioning
=============================

https://github.com/malie/multilevel-graph-partitioning


state
=====
coarsening and slow partitioning of a small, coarse graph work somewhat


otherwise
=========

heavily unfinished!


example
=======

    > printGraph testGraph2
    Graph
      ...
      edgeNodes:
        (Edge 1,(Node 100,Node 200))
        (Edge 2,(Node 100,Node 110))
        (Edge 3,(Node 110,Node 200))
        (Edge 4,(Node 200,Node 300))
        (Edge 5,(Node 200,Node 210))
        (Edge 6,(Node 210,Node 220))
        (Edge 7,(Node 220,Node 300))
        (Edge 8,(Node 300,Node 400))
        (Edge 9,(Node 300,Node 310))
        (Edge 10,(Node 310,Node 400))
        (Edge 11,(Node 400,Node 410))
        (Edge 12,(Node 400,Node 500))
        (Edge 13,(Node 410,Node 500))
        (Edge 14,(Node 500,Node 600))
        (Edge 15,(Node 600,Node 610))
        (Edge 16,(Node 600,Node 100))
        (Edge 17,(Node 610,Node 100))


    > mapM_ print . M.toList =<< partitionSlow testGraph2 4 MinimalCuts

    ...
    (ce:7.0 ib:2.0)
    (Node 100,2)
    (Node 110,2)
    (Node 200,3)
    (Node 210,3)
    (Node 220,3)
    (Node 300,1)
    (Node 310,1)
    (Node 400,1)
    (Node 410,0)
    (Node 500,0)
    (Node 600,2)
    (Node 610,2)

