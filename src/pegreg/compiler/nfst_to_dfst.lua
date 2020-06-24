-- TODO: CLEANUP both Reify and NFST_TO_DFST so that there's
-- not so much breaking of abstraction (sharing metatables etc.)
-- Cleanup reify so that creating a list doesn't have polynomial behavior.
-- Cleanup NFST_TO_DFST so that it doesn't use the graph library,
-- or alternatively modify the graph library so that it doens't
-- pull in so many dependencies.
local graph = require("graph")

local data_structures = require("pegreg.data_structures")
local list = data_structures.list
local nfst = data_structures.nfst

local nfst_to_dfst = {}

function nfst_to_dfst.sort_reified(reified)
   list.sort(reified.states)
   list.sort(reified.arrows)
end

local function nub(lst)
   local out = list.new()
   if #lst > 0 then
      local prev = lst:get(1)
      list.insert(out, lst:get(1))
      for i = 2, #lst, 1 do
         if prev ~= lst:get(i) then
            list.insert(out, lst:get(i))
         end
         prev = lst:get(i)
      end
   end
   return out
end

function nfst_to_dfst.nub(reified)
   nfst_to_dfst.sort_reified(reified)
   reified.states = nub(reified.states)
   reified.arrows = nub(reified.arrows)
   return reified
end

--------------------------------------------------------------------------------
-- Given an array, make an iterator over it
-- TODO move this to a utility file
--------------------------------------------------------------------------------
local function make_it(arr)
   local idx = 1
   local function it()
      if idx <= #arr then
         local out = arr[idx]
         idx = idx + 1
         return out
      else
         return nil
      end
   end
   return it
end

--------------------------------------------------------------------------------
-- TODO Move this as well
--------------------------------------------------------------------------------
local function make_list_it(lst)
   local idx = 1
   local function it()
      if idx <= #lst then
         local out = lst:get(idx)
         idx = idx + 1
         return out
      else
         return nil
      end
   end
   return it
end

--------------------------------------------------------------------------------
-- Take REIFIED, a reified set of states and arrows,
-- and create something that conforms to the
-- NFA interface defined in the file
-- nfa_to_dfa.lua
--------------------------------------------------------------------------------
function nfst_to_dfst.reified_to_nfa(reified)
   -- First, nub and sort
   nfst_to_dfst.nub(reified)

   -- Now, make wrappers for all of the states
   local state_to_state_wrapper = {}
   local state_to_arrows = {}
   for _, state in ipairs(reified.states) do
      local state_wrapper = {state = state}
      state_to_state_wrapper[state.number] = state_wrapper
      state_to_arrows[state.number] = {}

      function state_wrapper:number()
         return self.state.number
      end
      function state_wrapper:final()
         return self.state.final
      end

      for _, arrow in ipairs(reified.arrows) do
         if arrow.from == state.number then
            table.insert(state_to_arrows[state.number], arrow)
         end
         -- Sort to make the order of the arrows
         -- deterministic
         table.sort(state_to_arrows[state.number],
                    function (a, b)
                       return a.to < b.to
                    end)
      end
   end

   -- Now, make wrappers for all the arrows
   local arrow_to_arrow_wrapper = {}
   for _, arrow in ipairs(reified.arrows) do
      local arrow_wrapper = {arrow = arrow}
      arrow_to_arrow_wrapper[arrow] = arrow_wrapper

      function arrow_wrapper:from()
         return state_to_state_wrapper[self.arrow.from]
      end

      function arrow_wrapper:to()
         return state_to_state_wrapper[self.arrow.to]
      end

      function arrow_wrapper:input()
         return self.arrow.input
      end

      --------------------------------------------------------------------------
      -- Re expose the output character
      --------------------------------------------------------------------------
      function arrow_wrapper:output()
         return self.arrow.output
      end
   end

   -- Finally, wrap the whole NFA
   local nfa = {}
   function nfa:outgoing(state)
      return make_it(state_to_arrows[state:number()])
   end

   function nfa:states()
      local it = make_list_it(reified.states)
      local function wrapper()
         local v = it()
         return v and state_to_state_wrapper[v.number]
      end
      return wrapper
   end

   function nfa:arrows()
      local it = make_list_it(reified.arrows)
      local function wrapper()
         local v = it()
         return v and arrow_to_arrow_wrapper[v]
      end
      return wrapper
   end

   function nfa:start()
      return state_to_state_wrapper[reified.states:get(1).number]
   end

   return nfa
end

--------------------------------------------------------------------------------
-- Take REIFIED, a reified set of states and arrows,
-- G, an empty graph
-- and return the top vertex in the graph.
--------------------------------------------------------------------------------
function nfst_to_dfst.edge_list_to_graph(reified, g)
   reified.arrows:add(nfst.arrow.new(-1, 0, '', ''))
   nfst_to_dfst.sort_reified(reified)
   local number_to_vertex = {}

   local top = g:insert_vertex(reified.states:get(1))
   number_to_vertex[reified.states:get(1).number] = top

   for i = 2, #reified.states, 1 do
      local n = reified.states:get(i).number
      number_to_vertex[n] = g:insert_vertex(reified.states:get(i))
   end

   for _, arrow in ipairs(reified.arrows) do
      if number_to_vertex[arrow.from] and number_to_vertex[arrow.to] then
         g:insert_edge(number_to_vertex[arrow.from], number_to_vertex[arrow.to], arrow)
      end
   end
   return top
end

--------------------------------------------------------------------------------
-- Add to REACHABLE all of the verticies reachable by
-- epsilon transition from VERTEX,
-- and add to TRANSITIONS all of the transitions
-- not reachable by epsilon transition.
-- Furthermore, set the array
-- ISFINAL's index of one to whether
-- or not the epsilon closure is final
-- Return REACHABLE.
--------------------------------------------------------------------------------
function nfst_to_dfst.reachable(vertex, reachable, transitions, isfinal)
   reachable:add(vertex)
   -- TODO remove this check
   if isfinal ~= nil then
      isfinal[1] = isfinal[1] or vertex.data.final
   end
   for other_vertex, edge in pairs(vertex.adjacencies) do
      local c = edge.data.input
      if c == '' then
         nfst_to_dfst.reachable(other_vertex, reachable, transitions, isfinal)
      else
         if transitions[c] == nil then
            transitions[c] = list.new()
         end
         transitions[c]:add(edge)
      end
   end
   return reachable
end

--------------------------------------------------------------------------------
-- Ordered pair iterator generator
--------------------------------------------------------------------------------
local function opairs(t)
   local keys = {}
   for k, _ in pairs(t) do
      table.insert(keys, k)
   end
   table.sort(keys)
   local function onext(t, n)
      if n + 1 > #keys then
         return nil
      end
      return n + 1, keys[n+1], t[keys[n + 1]]
   end
   return onext, t, 0
end

--------------------------------------------------------------------------------
-- Create a new graph wrapping the old graph.
-- The new graph's verticies will be the
-- epsilon closures of the old graph's verticies
-- arranged into an array of verticies.
-- The new graph's edges will be based on the old graph's edges.
-- Return the graph, the toppmost vertex,
-- and a table to from epsilon closures to whether they
-- are final or not.
--------------------------------------------------------------------------------
function nfst_to_dfst.reachable_g(g, top)
   local vertex_to_transitions = {}
   local reachable = graph.graph.new()

   local reachable_from_top = list.new()
   local transitions = {}
   local isfinal = {[1] = false}
   local vertex_to_final = {}
   nfst_to_dfst.reachable(top, reachable_from_top, transitions, isfinal)
   local out = reachable:insert_vertex(reachable_from_top)
   vertex_to_transitions[out] = transitions
   vertex_to_final[out] = isfinal[1]

   for vertex in g:verticies() do
      local reachable_states = list.new()
      local transitions = {}
      local isfinal = {[1] = false}
      nfst_to_dfst.reachable(vertex, reachable_states, transitions, isfinal)
      local vtx = reachable:insert_vertex(reachable_states)
      vertex_to_transitions[vtx] = transitions
      vertex_to_final[vtx] = isfinal[1]
   end

   for vertex, transitions in pairs(vertex_to_transitions) do
      for _, _, edge_list in opairs(transitions) do
         for _, edge in ipairs(edge_list) do
            local arrow = edge.data
            for other_vertex in reachable:verticies() do
               local nfst_verticies = other_vertex.data
               local arrow_exists = false
               for _, nfst_vertex in ipairs(nfst_verticies) do
                  local nfst_state = nfst_vertex.data
                  if nfst_state.number == arrow.to then
                     arrow_exists = true
                  end
               end
               if arrow_exists then
                  -- The arrow won't have the right numbers.
                  -- That's ok, we just need to keep track of it
                  -- for its character.
                  reachable:insert_edge(vertex, other_vertex, arrow)
               end
            end
         end
      end
   end

   return reachable, out, vertex_to_final
end

--------------------------------------------------------------------------------
-- Find the DFST from the reachable graph, its top vertex,
-- and a map from each veterx to whether or not iti s final
--------------------------------------------------------------------------------
function nfst_to_dfst.find_dfst_from_reachable(reachable, top, vertex_to_final)
   local pruned_g, pruned_top = graph.spanning_tree(top)
   local vertex_to_state_number = {}
   local number_to_final = {}
   local n = 0
   vertex_to_state_number[top] = 0
   number_to_final[0] = vertex_to_final[top]

   for vertex in pruned_g:verticies() do
      if vertex ~= pruned_top then
         n = n + 1
         vertex_to_state_number[vertex.data] = n
         number_to_final[n] = vertex_to_final[vertex.data]
      end
   end

   local new_arrows = list.new()

   for vertex in pruned_g:verticies() do
      for other_vertex, edge in pairs(vertex.data.adjacencies) do
         local from = vertex_to_state_number[vertex.data]
         local to = vertex_to_state_number[other_vertex]
         local old_arrow = edge.data
         local input = old_arrow.input
         local output = old_arrow.output
         local arrow = nfst.arrow.new(from, to, input, output)
         new_arrows:add(arrow)
      end
   end

   local new_states = list.new()

   for i = 0, n, 1 do
      new_states:add(nfst.state.new(i, number_to_final[i]))
   end

   return nfst.nfst.new(new_states, new_arrows)
end

return nfst_to_dfst
