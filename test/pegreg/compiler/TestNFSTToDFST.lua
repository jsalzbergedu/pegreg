require("test.pegreg.interpreters.TestReify")
local pegreg = require("pegreg")
local luaunit = require("luaunit")
local graph = require("graph")

local nfst_to_dfst = pegreg.nfst_to_dfst

local reify = pegreg.reify

TestNFSTToDFST = {}


function TestNFSTToDFST:testNub()
   print()
   print("Testing nub")
   print(nfst_to_dfst.nub(TestReify.make_reified()))
end

function TestNFSTToDFST:testEdgeListToGraph()
   g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(TestReify.make_reified(), g)
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
      table.insert(expected_reachable, reify.state(i, false):get(1))
   end
   luaunit.assertEquals(reachable_data, expected_reachable)
   -- TODO test transitions table
end

-- NFST with branching and rejoining
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
-- 6    | 7  | x:x
local function make_rejoining_nfst()
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
   arrows = p(a(3, 5, 'a', 'a'), arrows)
   arrows = p(a(4, 6, '', ''), arrows)
   arrows = p(a(5, 6, '', ''), arrows)
   arrows = p(a(6, 7, 'x', 'x'), arrows)
   return reify.create(states, arrows)
end

function TestNFSTToDFST:testDfstRejoining()
   local g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(make_rejoining_nfst(), g)
   local reachable, top_reachable, vertex_to_final = nfst_to_dfst.reachable_g(g, top)
   local actual_dfst = nfst_to_dfst.find_dfst_from_reachable(reachable, top_reachable, vertex_to_final)

   local expected_dfst = [[
(reified (states ((state 0 false) (state 1 false) (state 2 false) (state 3 true))) (arrows ((arrow 0 1 a a) (arrow 0 2 b b) (arrow 1 3 x x) (arrow 2 3 x x))))]]
   luaunit.assertEquals(tostring(actual_dfst), expected_dfst)
end

function TestNFSTToDFST:testReachableG()
   print("Testing reachable G")
   local g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(make_rejoining_nfst(), g)
   local reachable, top_reachable, vertex_to_final = nfst_to_dfst.reachable_g(g, top)
   -- If you want to see the generated graph,
   -- uncomment the following line.
   -- graph.plantuml(reachable)
end

function TestNFSTToDFSTFromReachable()
   print("Testing reachable G")
   local g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(make_rejoining_nfst(), g)
   local reachable, top_reachable, vertex_to_final = nfst_to_dfst.reachable_g(g, top)
   local reified = nfst_to_dfst.find_dfst_from_reachable(reachable, top_reachable, vertex_to_final)
   print(reified)
end
