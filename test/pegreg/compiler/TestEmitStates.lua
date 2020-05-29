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
   local states, transitions = nfst_to_dfst.find_states(top)
   local dfst = nfst_to_dfst.dfst(states, transitions)
   local it = emit_states.from_dfst(dfst)
   local outstr, match_success, matched_states = it:match_string("bbx")
   luaunit.assertEquals(outstr, "bbx")
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {2, 3, 4})
   local outstr, match_success, matched_states = it:match_string("aax")
   luaunit.assertEquals(outstr, "aax")
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {1, 5, 6})
   local outstr, match_success, matched_states = it:match_string("aaxy")
   luaunit.assertEquals(outstr, "aax")
   luaunit.assertFalse(match_success)
   luaunit.assertEquals(matched_states, {1, 5, 6})
   local outstr, match_success, matched_states = it:match_string("a")
   luaunit.assertEquals(outstr, "a")
   luaunit.assertFalse(match_success)
   luaunit.assertEquals(matched_states, {1})
end
