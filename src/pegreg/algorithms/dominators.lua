--------------------------------------------------------------------------------
-- Dominator finding algorithm adapted from the networkx library.
--------------------------------------------------------------------------------

--- Module containing funcitons for finding dominators.
--- The graphs used by this algorithm must conform to the interface specified
--- in @see Graph.
local dominators = {}

local function preds(graph, node)
   local arr = {}
   for edge in graph:incoming_edges(node) do
      table.insert(arr, graph:opposite(node, edge))
   end
   return arr
end

local function reduce(binop, arr)
   if #arr < 1 then
      error("Reduce on an empty sequence")
   end

   if #arr < 2 then
      return arr[1]
   end

   local val = binop(arr[1], arr[2])

   for i = 3, #arr, 1 do
      val = binop(val, arr[i])
   end

   return val
end

--------------------------------------------------------------------------------
-- An annotated, depth first search.
-- Using GRAPH and NODE, as well as
-- BEGIN, an initially empty map from nodes to the time they were found
-- FINISH, an initially empty map from nodes to the time they finished
-- processing
-- PARENT, the parent of the node, initially nil,
-- PARENTS, a map from each node to its discovered parent (or nil)
-- CLOCK, a reference to the time (initially {0})
-- and FOUND, an initially empty map from each node to whether or not it is
-- found,
-- compute an annotated dfs stored begin, finish, and parent.
--
-- Algorithm borrowed from
-- https://www.cs.yale.edu/homes/aspnes/pinewiki/DepthFirstSearch.html
--------------------------------------------------------------------------------
local function time_dfs_rec(graph, node, begin, finish, parent, parents, clock, found)
   parents[node] = parent
   begin[node] = clock[1]
   clock[1] = clock[1] + 1
   found[node] = true
   for child in graph:children(node) do
      if found[child] == nil then
         time_dfs_rec(graph, child, begin, finish, node, parents, clock, found)
      end
   end
   finish[node] = clock[1]
   clock[1] = clock[1] + 1
end

--------------------------------------------------------------------------------
-- An annotated, depth first search
-- Using GRAPH and NODE,
-- return a map from each node to the time it started processing
-- a map from each node to the time it finished processing
-- and a map from each node to its parents
-- Algorithm borrowed from
-- https://www.cs.yale.edu/homes/aspnes/pinewiki/DepthFirstSearch.html
--------------------------------------------------------------------------------
local function time_dfs(graph, node)
   local begin = {}
   local finish = {}
   local parent = nil
   local parents = {}
   local clock = {0}
   local found = {}
   time_dfs_rec(graph, node, begin, finish, parent, parents, clock, found)
   return begin, finish, parents
end

-- Get postorder ordering of graph
local function dfs_postorder(graph, node)
   local _, finish, _ = time_dfs(graph, node)
   local function lt_edge(e1, e2)
      return finish[e1] < finish[e2]
   end
   local verticies = {}
   for vertex in graph:verticies() do
      table.insert(verticies, vertex)
   end
   table.sort(verticies, lt_edge)
   return verticies
end

--------------------------------------------------------------------------------
-- Using GRAPH and NODE,
-- where GRAPH is a directed graph and NODE
-- is the topmost node in the graph,
-- find the immediate dominator of each node and return it
-- as a map from nodes to their immediate dominator.
-- Based completely on networkx' implementation
-- (https://networkx.github.io/documentation/networkx-1.10/reference/generated/networkx.algorithms.dominance.immediate_dominators.html)
--------------------------------------------------------------------------------
function dominators.dominators(graph, node)
   if not graph:contains(node) then
      error("Graph does not contain node")
   end

   local idom = {[node] = node}
   local order = dfs_postorder(graph, node)
   local dfn = {}
   for i, v in ipairs(order) do
      dfn[v] = i
   end

   order[#order] = nil

   local reverse = {}
   for i = #order, 1, -1 do
      reverse[#order - i + 1] = order[i]
   end

   order = reverse

   local function intersect(u, v)
      while u ~= v do
         while dfn[u] < dfn[v] do
            u = idom[u]
         end
         while dfn[u] > dfn[v] do
            v = idom[v]
         end
      end
      return u
   end

   local changed = true
   while changed do
      changed = false
      for _, u in ipairs(order) do
         local idom_preds = {}
         for _, v in ipairs(preds(graph, u)) do
            if idom[v] ~= nil then
               table.insert(idom_preds, v)
            end
         end
         local new_idom = reduce(intersect, idom_preds)
         if idom[u] ~= new_idom then
            idom[u] = new_idom
            changed = true
         end
      end
   end

   return idom
end

--------------------------------------------------------------------------------
-- Return whether X is dominated by Y
--------------------------------------------------------------------------------
function dominators.dominated_by(idom, x, y)
   if x == y then
      return true
   end

   while idom[x] ~= nil do
      if x == idom[x] then
         return false
      end

      if idom[x] == y then
         return true
      end
      x = idom[x]
   end
   return false
end

return dominators
