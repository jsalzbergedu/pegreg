local luaunit = require("luaunit")
local pegreg = require("pegreg")
local dominators = pegreg.dominators

TestDominators = {}

--------------------------------------------------------------------------------
-- Get a graph with the specified interface from
-- edges (like so: {{0, 1}, {1, 2}, ...})
--------------------------------------------------------------------------------
function TestDominators:fromEdges(edges)
   local impl = {}

   function impl:start()
      return edges[1][1]
   end

   function impl:opposite(node, edge)
      if node == edge[1] then
         return edge[2]
      end

      return edge[1]
   end

   function impl:incoming_edges(node)
      local edge_list = {}
      for _, edge in ipairs(edges) do
         if edge[2] == node then
            table.insert(edge_list, edge)
         end
      end
      table.sort(edge_list, function (a, b) return a[1] < b[1] end)
      local idx = 1
      local function it()
         if idx > #edge_list then
            return nil
         end
         local out = edge_list[idx]
         idx = idx + 1
         return out
      end
      return it
   end

   function impl:contains(node)
      for _, edge in ipairs(edges) do
         if edge[1] == node then
            return true
         end
         if edge[2] == node then
            return true
         end
      end
      return false
   end

   function impl:children(node)
      local children = {}
      for _, edge in ipairs(edges) do
         if edge[1] == node then
            table.insert(children, edge[2])
         end
      end
      table.sort(children)
      local idx = 1
      local function it()
         if idx > #children then
            return nil
         end
         local out = children[idx]
         idx = idx + 1
         return out
      end
      return it
   end

   for _, edge in ipairs(edges) do
      local edge_impl = {}
      function edge_impl:from()
         return edge[1]
      end
      function edge_impl:to()
         return edge[2]
      end
      edge = setmetatable(edge, {__index = edge_impl})
   end

   function impl:edges()
      local idx = 1
      local function it()
         if idx > #edges then
            return nil
         end
         local out = edges[idx]
         idx = idx + 1
         return out
      end
      return it
   end

   local verticies = {}
   local vtx_found = {}
   for _, edge in ipairs(edges) do
      if vtx_found[edge[1]] == nil then
         vtx_found[edge[1]] = edge[1]
         table.insert(verticies, edge[1])
      end
      if vtx_found[edge[2]] == nil then
         vtx_found[edge[2]] = edge[2]
         table.insert(verticies, edge[2])
      end
   end

   table.sort(verticies)

   function impl:verticies()
      local idx = 1
      local function it()
         if idx > #verticies then
            return nil
         end
         local out = verticies[idx]
         idx = idx + 1
         return out
      end
      return it
   end

   return setmetatable(edges, {__index = impl})
end

function TestDominators.example_graph()
   local edges = {{0, 1}, {1, 2}, {1, 3}, {2, 7}, {3, 4}, {4, 5}, {4, 6},
      {5, 7}, {6, 4}}
   local graph = TestDominators:fromEdges(edges)
   return graph
end


--------------------------------------------------------------------------------
-- Based on networkx' test
-- that uses the example from boost's graph library
--------------------------------------------------------------------------------
function TestDominators:testBoost()
   local graph = TestDominators.example_graph()
   local dominator_map = dominators.dominators(graph, 0)

   local expected = {
      [0] = 0,
      0,
      1,
      1,
      3,
      4,
      4,
      1,
   }

   luaunit.assertEquals(dominator_map, expected)
end
