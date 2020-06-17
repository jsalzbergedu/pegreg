require("test.pegreg.interpreters.TestReify")
local pegreg = require("pegreg")
local luaunit = require("luaunit")
local graph = require("graph")

local emit_states = pegreg.emit_states
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

TestEmitStates = {}

function TestEmitStates:testEmitStatesOutput()
   local g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(TestReify.make_reified(), g)
   local reachable, top_reachable, vertex_to_final = nfst_to_dfst.reachable_g(g, top)
   local dfst = nfst_to_dfst.find_dfst_from_reachable(reachable, top_reachable, vertex_to_final)
   local it = emit_states.from_dfst(dfst)
   local outstr, match_success, matched_states = it:match_string("bbx")
   luaunit.assertEquals(outstr, "bbx")
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {2, 4, 5})
   local outstr, match_success, matched_states = it:match_string("aax")
   luaunit.assertEquals(outstr, "aax")
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {1, 3, 5})
   local outstr, match_success, matched_states = it:match_string("aaxy")
   luaunit.assertEquals(outstr, "aax")
   luaunit.assertFalse(match_success)
   luaunit.assertEquals(matched_states, {1, 3, 5, 6})
   local outstr, match_success, matched_states = it:match_string("a")
   luaunit.assertEquals(outstr, "a")
   luaunit.assertFalse(match_success)
   luaunit.assertEquals(matched_states, {1})
end

local function make_star()
   local l = l.l()
   local reified = l:grammar(l:seq(l:star(l:lit('a')), l:lit('b')))
      :create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(state_arrow)(flatten)(reify)
   return reified
end

function TestEmitStates:testStar()
   local g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(make_star(), g)
   local reachable, top_reachable, vertex_to_final = nfst_to_dfst.reachable_g(g, top)
   local dfst = nfst_to_dfst.find_dfst_from_reachable(reachable, top_reachable, vertex_to_final)
   local it = emit_states.from_dfst(dfst)
   local outstr, match_success, matched_states = it:match_string("aaaab")
   luaunit.assertEquals(outstr, "aaaab")
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {1, 1, 1, 1, 2})
end

function TestEmitStates:testAStarA()
   print("Testing emit states (a*)a")
   local l = l.l()
   local reified = l:grammar(l:seq(l:star(l:lit('a')), l:lit('a')))
      :create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(state_arrow)(flatten)(reify)

   print("Reified is: ", reified)

   local g = graph.graph.new()
   local top = nfst_to_dfst.edge_list_to_graph(reified, g)
   local reachable, top_reachable, vertex_to_final = nfst_to_dfst.reachable_g(g, top)
   local dfst = nfst_to_dfst.find_dfst_from_reachable(reachable, top_reachable, vertex_to_final)
   print("dfst is:", dfst)
   local it = emit_states.from_dfst(dfst)
end
