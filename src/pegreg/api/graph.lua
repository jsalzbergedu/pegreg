--------------------------------------------------------------------------------
-- Type signatures for a graph data type.
--
-- the NODEs themselves must be
-- #1: Hashable
-- #2: Comparable via ~= and =
--------------------------------------------------------------------------------

--- The graph datatype.
--- @class Graph
local graph = {}

--- Given a NODE and an EDGE, return the node in the
--- EDGE that is not NODE.
--- @generic V, E
--- @param node V the node
--- @param edge E the edge
--- @return V opposite the opposite node
function graph:opposite(node, edge)
   error("not implemented" .. tostring(node) .. tostring(edge))
end

--- given a NODE, find the incoming edges to NODE.
--- @generic V, E
--- @param node V the node
--- @return fun(): E iterator incoming edges on the node
function graph:incoming_edges(node)
   error("not implemented" .. tostring(node))
end

--- Given a NODE, find the children of the said node
--- @generic V
--- @param node V the node
--- @return fun(): V iterator over the children of the node
function graph:children(node)
   error("Not implemented" .. tostring(node))
end

--- Return an iterator over all of the edges of the graph
--- @generic E
--- @return fun(): E an iterator over the edges
function graph:edges()
end

--- Return an iterator over all of the verticies of the graph
--- @generic V
--- @return fun(): V an iterator over the verticies
function graph:verticies()
end

--- return a starting vertex for the graph
--- @generic V
--- @return V vertex the starting vertex
function graph:start()
   return v
end

return graph
