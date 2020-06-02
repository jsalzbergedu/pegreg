-- TODO: CLEANUP both Reify and NFST_TO_DFST so that there's
-- not so much breaking of abstraction (sharing metatables etc.)
-- Cleanup reify so that creating a list doesn't have polynomial behavior.
-- Cleanup NFST_TO_DFST so that it doesn't use the graph library,
-- or alternatively modify the graph library so that it doens't
-- pull in so many dependencies.
local interpreters = require("pegreg.interpreters")
local graph = require("graph")

local reify = interpreters.reify

local nfst_to_dfst = {}

function nfst_to_dfst.sort_reified(reified)
   table.sort(reified.states)
   table.sort(reified.arrows)
end

local function nub(lst)
   local out = {}
   if #lst > 0 then
      local prev = lst[1]
      table.insert(out, lst[1])
      for i = 2, #lst, 1 do
         if prev ~= lst[i] then
            table.insert(out, lst[i])
         end
         prev = lst[i]
      end
   end
   return out
end

function nfst_to_dfst.nub(reified)
   nfst_to_dfst.sort_reified(reified)
   reified.states = nub(reified.states)
   setmetatable(reified.states, reify.pair_mt)
   reified.arrows = nub(reified.arrows)
   setmetatable(reified.arrows, reify.pair_mt)
   return reified
end

--------------------------------------------------------------------------------
-- Take REIFIED, a reified set of states and arrows,
-- G, an empty graph
-- and return the top vertex in the graph.
--------------------------------------------------------------------------------
function nfst_to_dfst.edge_list_to_graph(reified, g)
   nfst_to_dfst.sort_reified(reified)
   local number_to_vertex = {}

   reified.arrows = reify.pair(reify.arrow(-1, 0, '', ''), reified.arrows)

   local top = g:insert_vertex(reified.states[1])
   number_to_vertex[reified.states[1].number] = top

   for i = 2, #reified.states, 1 do
      local n = reified.states[i].number
      number_to_vertex[n] = g:insert_vertex(reified.states[i])
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
   table.insert(reachable, vertex)
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
            transitions[c] = {}
         end
         table.insert(transitions[c], edge)
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

   local reachable_top = {}
   local transitions = {}
   local isfinal = {[1] = false}
   local vertex_to_final = {}
   nfst_to_dfst.reachable(top, reachable_top, transitions, isfinal)
   -- table.insert(all_transitions, transitions)
   local out = reachable:insert_vertex(reachable_top)
   vertex_to_transitions[out] = transitions
   vertex_to_final[out] = isfinal[1]

   for vertex in g:verticies() do
      local reachable_states = {}
      local transitions = {}
      local isfinal = {[1] = false}
      nfst_to_dfst.reachable(vertex, reachable_states, transitions, isfinal)
      local vtx = reachable:insert_vertex(reachable_states)
      vertex_to_transitions[vtx] = transitions
      vertex_to_final[vtx] = isfinal[1]
   end

   for vertex, transitions in pairs(vertex_to_transitions) do
      for _, c, edge_list in opairs(transitions) do
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

   -- local pruned_reachable = graph.graph.new()
   -- local pruned_top, pruned_g = graph.spanning_tree(out)

   -- local vertex_to_state_number = {}
   -- local n = 0
   -- vertex_to_state_number[pruned_top] = 0

   -- for vertex in pruned_g:verticies() do
   --    if vertex ~= pruned_top then
   --       n = n + 1
   --       vertex_to_state_number[vertex] = n
   --    end
   -- end

   -- for vertex in pruned_g:verticies() do

   -- end
   return reachable, out, vertex_to_final
end

--------------------------------------------------------------------------------
-- Find the DFST from the reachable graph, its top vertex,
-- and whether the top vertex is final
--------------------------------------------------------------------------------
function nfst_to_dfst.find_dfst_from_reachable(reachable, top, vertex_to_final)
   local pruned_reachable = graph.graph.new()
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

   local new_arrows = {}

   for vertex in pruned_g:verticies() do
      for other_vertex, edge in pairs(vertex.data.adjacencies) do
         local from = vertex_to_state_number[vertex.data]
         local to = vertex_to_state_number[other_vertex]
         local old_arrow = edge.data
         local input = old_arrow.input
         local output = old_arrow.output
         local arrow = reify.arrow(from, to, input, output)[1]
         table.insert(new_arrows, arrow)
      end
   end

   local new_states = {}
   setmetatable(new_states, reify.pair_mt)

   for i = 0, n, 1 do
      table.insert(new_states, reify.state(i, number_to_final[i])[1])
   end

   table.sort(new_arrows)
   new_arrows = nub(new_arrows)
   setmetatable(new_arrows, reify.pair_mt)

   return reify.create(new_states, new_arrows)
end

--------------------------------------------------------------------------------
-- Given the top state in a graph, TOP,
-- find the states and transitions in an fst
-- and return them.
--------------------------------------------------------------------------------
function nfst_to_dfst.find_states(top)
   -- First, find the states reachable from the top.
   local dfst_states = {}
   local dfst_transitions = {}
   local reachable = {}
   local transitions = {}
   local state_to_number = {}
   nfst_to_dfst.reachable(top, reachable, transitions)
   table.insert(dfst_states, reachable)
   -- Then, recurse through the states that could not
   -- be reached by epsilon transition.
   -- Keep track of these via a stack of
   -- {N, TRANSITIONS}
   -- where N is the DFST state number
   -- and TRANSITIONS is a list
   -- of verticies to transition to
   local transitions_stack = {}

   if next(transitions) ~= nil then
      table.insert(transitions_stack, {0, transitions})
   end
   while #transitions_stack > 0 do
      local n, stack_top =
         unpack(transitions_stack[#transitions_stack])
      transitions_stack[#transitions_stack] = nil
      for _, c, edge_list in opairs(stack_top) do
         transitions = {}
         reachable = {}
         for _, edge in ipairs(edge_list) do
            -- Keep adding reachable and transitions to the
            -- same lists/tables
            nfst_to_dfst.reachable(edge.to, reachable, transitions)
         end
         table.insert(dfst_states, reachable)
         table.insert(dfst_transitions, reify.arrow(n, #dfst_states - 1,
                                                    c, c)[1])
         if next(transitions) ~= nil then
            table.insert(transitions_stack, {#dfst_states - 1, transitions})
         end
      end
   end

   -- Sort and nub the states
   for _, v in ipairs(dfst_states) do
      table.sort(v)
   end
   for i, v in ipairs(dfst_states) do
      dfst_states[i] = nub(v)
   end

   -- Sort and nub the transitions
   table.sort(dfst_transitions)
   dfst_transitions = nub(dfst_transitions)
   return dfst_states, dfst_transitions
end

--------------------------------------------------------------------------------
-- Takes DFST_STATES and DFST_TRANSITIONS,
-- the two tables created by find_states,
-- and creates a reified DFST.
--------------------------------------------------------------------------------
function nfst_to_dfst.dfst(dfst_states, dfst_transitions)
   local states = reify.null()
   local arrows = reify.null()
   for i, vertex_list in ipairs(dfst_states) do
      local final = false
      for _, state in ipairs(vertex_list) do
         final = state.data.final or final
      end
      states = reify.pair(reify.state(i - 1, final), states)
   end
   for _, v in ipairs(dfst_transitions) do
      local arrow = {v}
      setmetatable(arrow, reify.pair_mt)
      arrows = reify.pair(arrow, arrows)
   end
   local reified = reify.create(states, arrows)
   nfst_to_dfst.sort_reified(reified)
   return reified
end

--------------------------------------------------------------------------------
-- Takes in TOP, the top vertex of the NFST,
-- N, the current number
-- REIFIED, an empty reify construct,
-- and ASSMT, an empty table of assignments
-- from NFST states to DSFT states.
-- Builds on and returns REIFIED.
--------------------------------------------------------------------------------
function nfst_to_dfst.convert(top, n, reified, assmt)
   local stack = {}
   local possible_through_epsilon = {}
   while #stack > 0 do
      local top = stack[#stack]
      stack[#stack] = nil
   end
end

return nfst_to_dfst
