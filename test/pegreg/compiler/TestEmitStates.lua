require("test.pegreg.interpreters.TestReify")
local pegreg = require("pegreg")
local luaunit = require("luaunit")
local graph = require("graph")

local emit_states = pegreg.emit_states

local nfst_to_dfst = pegreg.nfst_to_dfst

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
   luaunit.assertEquals(matched_states, {1, 3, 5})
   local outstr, match_success, matched_states = it:match_string("a")
   luaunit.assertEquals(outstr, "a")
   luaunit.assertFalse(match_success)
   luaunit.assertEquals(matched_states, {1})
end
