local pegreg = require("pegreg")
local luaunit = require("luaunit")
local graph = require("graph")

local nfst_to_dfst = pegreg.nfst_to_dfst

local l = pegreg.language
local expand_ref = pegreg.expand_ref
local expand_string = pegreg.expand_string
local add_left_right = pegreg.add_left_right
local mark_fin = pegreg.mark_fin
local enumerate = pegreg.enumerate
local state_arrow = pegreg.state_arrow
local flatten = pegreg.flatten
local print_n = pegreg.print_n
local print_fst = pegreg.print_fst
local reify = pegreg.reify

TestNFSTToDFST = {}


local function make_reified()
   local l = l.l()
   local reified = l:rule('A'):is(l:lit('aa'))
      :rule('B'):is(l:lit('bb'))
      :rule('K'):is(l:lit('x'))
      :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
      :create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(state_arrow)(flatten)(reify)
   return reified
end

function TestNFSTToDFST:testNub()
   print()
   print("Testing nub")
   print(nfst_to_dfst.nub(make_reified()))
end

function TestNFSTToDFST:testEdgeListToGraph()
   g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(make_reified(), g)
   -- TODO insert more tests here
end

-- NFST with branching and redundant states:
-- States: 0, 1, 2, 3, 4, 5, 6, 7
-- Final states: 7
-- Transitions:
-- from | to | tape
-- 0    | 1  | 0:0
-- 1    | 2  | 0:0
-- 1    | 3  | 0:0
-- 2    | 4  | a:a
-- 3    | 5  | b:b
-- 4    | 6  | 0:0
-- 5    | 6  | 0:0
-- 6    | 7  | 0:0
local function make_dummy_nfst()
   local p = reify.pair
   local s = reify.state
   local a = reify.arrow
   local states = reify.null()
   local arrows = reify.null()
   for i = 0, 6 do
      states = reify.pair(s(i, false), states)
   end
   states = p(s(7, true), states)
   arrows = p(a(0, 1, '', ''), arrows)
   arrows = p(a(1, 2, '', ''), arrows)
   arrows = p(a(1, 3, '', ''), arrows)
   arrows = p(a(2, 4, 'a', 'a'), arrows)
   arrows = p(a(3, 5, 'b', 'b'), arrows)
   arrows = p(a(4, 6, '', ''), arrows)
   arrows = p(a(5, 6, '', ''), arrows)
   arrows = p(a(6, 7, '', ''), arrows)
   return reify.create(states, arrows)
end

function TestNFSTToDFST:testReachable()
   local g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(make_dummy_nfst(), g)
   local reachable = {}
   local transitions = {}
   nfst_to_dfst.reachable(top, reachable, transitions)
   local reachable_data = {}
   for _, v in ipairs(reachable) do
      table.insert(reachable_data, v.data)
   end
   local expected_reachable = {}
   for i = 0, 3 do
      table.insert(expected_reachable, reify.state(i, false)[1])
   end
   luaunit.assertEquals(reachable_data, expected_reachable)
   -- TODO test transitions table
end

function TestNFSTToDFST:testFindStates()
   print("Testing find states")
   local g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(make_dummy_nfst(), g)
   local states, transitions = nfst_to_dfst.find_states(top)
   local actual_states = "\n"
   for i, v in ipairs(states) do
      actual_states = actual_states .. tostring(i) .. "\n"
      for _, o in ipairs(v) do
         actual_states = actual_states .. tostring(o.data)
         actual_states = actual_states .. tostring(" ")
      end
      actual_states = actual_states .. "\n"
   end
   local expected_states =
      [[

1
(state 0 false) (state 1 false) (state 2 false) (state 3 false) 
2
(state 4 false) (state 6 false) (state 7 true) 
3
(state 5 false) (state 6 false) (state 7 true) 
]]
   luaunit.assertEquals(actual_states, expected_states)

   local actual_transitions = ""
   for _, v in ipairs(transitions) do
      actual_transitions = actual_transitions .. tostring(v) .. " "
   end
   print("actual transitions is: ", actual_transitions)
   local expected_transitions = "(arrow 1 2 a a) (arrow 1 3 b b) "
   luaunit.assertEquals(actual_transitions, expected_transitions)
end

-- NFST with branching and redundant transitions
-- States: 0, 1, 2, 3, 4, 5, 6, 7
-- Final states: 7
-- Transitions:
-- from | to | tape
-- 0    | 1  | 0:0
-- 1    | 2  | 0:0
-- 1    | 3  | 0:0
-- 2    | 4  | a:a
-- 3    | 5  | b:b
-- 4    | 6  | 0:0
-- 5    | 6  | 0:0
-- 6    | 7  | 0:0
local function make_redundant_nfst()
   local p = reify.pair
   local s = reify.state
   local a = reify.arrow
   local states = reify.null()
   local arrows = reify.null()
   for i = 0, 6 do
      states = reify.pair(s(i, false), states)
   end
   states = p(s(7, true), states)
   arrows = p(a(0, 1, '', ''), arrows)
   arrows = p(a(1, 2, '', ''), arrows)
   arrows = p(a(1, 3, '', ''), arrows)
   arrows = p(a(2, 4, 'b', 'b'), arrows)
   arrows = p(a(3, 5, 'b', 'b'), arrows)
   arrows = p(a(4, 6, '', ''), arrows)
   arrows = p(a(5, 6, '', ''), arrows)
   arrows = p(a(6, 7, '', ''), arrows)
   return reify.create(states, arrows)
end

function TestNFSTToDFST:testFindStatesRedundant()
   print("Testing find states")
   local g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(make_redundant_nfst(), g)
   local states, transitions = nfst_to_dfst.find_states(top)
   local actual_states = "\n"
   for i, v in ipairs(states) do
      actual_states = actual_states .. tostring(i) .. "\n"
      for _, o in ipairs(v) do
         actual_states = actual_states .. tostring(o.data)
         actual_states = actual_states .. tostring(" ")
      end
      actual_states = actual_states .. "\n"
   end
   local expected_states =
      [[

1
(state 0 false) (state 1 false) (state 2 false) (state 3 false) 
2
(state 4 false) (state 5 false) (state 6 false) (state 7 true) 
]]
   luaunit.assertEquals(actual_states, expected_states)

   local actual_transitions = ""
   for _, v in ipairs(transitions) do
      actual_transitions = actual_transitions .. tostring(v) .. " "
   end
   local expected_transitions = "(arrow 1 2 b b) "
   luaunit.assertEquals(expected_transitions, actual_transitions)
end

function TestNFSTToDFST:testDfst()
   print("Testing find states")
   local g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(make_dummy_nfst(), g)
   local states, transitions = nfst_to_dfst.find_states(top)
   local actual_dfst = nfst_to_dfst.dfst(states, transitions)
   local expected_dfst = [[
(reified (states ((state 1 false) (state 2 true) (state 3 true))) (arrows ((arrow 1 2 a a) (arrow 1 3 b b))))]]
   luaunit.assertEquals(tostring(actual_dfst), expected_dfst)
end
