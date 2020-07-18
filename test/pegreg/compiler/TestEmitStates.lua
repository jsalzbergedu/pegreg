require("test.pegreg.interpreters.TestReify")
local pegreg = require("pegreg")
local luaunit = require("luaunit")

local emit_states = pegreg.emit_states
local nfa_to_dfa = pegreg.nfa_to_dfa


local l = pegreg.language
local expand_ref = pegreg.expand_ref
local expand_string = pegreg.expand_string
local add_left_right = pegreg.add_left_right
local mark_fin = pegreg.mark_fin
local enumerate = pegreg.enumerate
local state_arrow = pegreg.state_arrow
local flatten = pegreg.flatten
local reify2 = pegreg.reify2

TestEmitStates = {}

function TestEmitStates:testEmitStatesOutput()
   local nfa = TestReify.make_reified()
   local dfa = nfa_to_dfa.decorate(nfa_to_dfa.determinize(nfa))
   local it = emit_states.from_abstract(dfa)

   local outstr, match_success, matched_states = it:match_string("bbx")
   luaunit.assertEquals(outstr, "bbx")
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {2, 3, 4})
   local outstr, match_success, matched_states = it:match_string("aax")
   luaunit.assertEquals(outstr, "aax")
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {1, 5, 4})
   local outstr, match_success, matched_states = it:match_string("aaxy")
   luaunit.assertEquals(outstr, "aax")
   luaunit.assertFalse(match_success)
   luaunit.assertEquals(matched_states, {1, 5, 4, 6})
   local outstr, match_success, matched_states = it:match_string("a")
   luaunit.assertEquals(outstr, "a")
   luaunit.assertFalse(match_success)
   luaunit.assertEquals(matched_states, {1})
end

local function make_star()
   local l = l.l()
   local reified = l:grammar(l:seq(l:star(l:lit('a')), l:lit('b')))
      :create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(state_arrow)(flatten)(reify2)
   return reified
end

function TestEmitStates:testStar()
   local nfa = make_star()
   local dfa = nfa_to_dfa.decorate(nfa_to_dfa.determinize(nfa))
   local it = emit_states.from_abstract(dfa)
   local outstr, match_success, matched_states = it:match_string("aaaab")
   luaunit.assertEquals(outstr, "aaaab")
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {1, 1, 1, 1, 2})
end

function TestEmitStates:testAStarA()
   local l = l.l()
   local nfa = l:grammar(l:seq(l:star(l:lit('a')), l:lit('a')))
      :create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(state_arrow)(flatten)(reify2)

   local dfa = nfa_to_dfa.decorate(nfa_to_dfa.determinize(nfa))
   local it = emit_states.from_abstract(dfa)
   local outstr, match_success, matched_states = it:match_string("aaaa")
   luaunit.assertEquals(outstr, "aaaa")
   luaunit.assertEquals(match_success, true)
   luaunit.assertEquals(matched_states, {1, 1, 1, 1})
end
