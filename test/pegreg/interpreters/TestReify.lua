require("test.pegreg.interpreters.TestCreateArrows")
require("test.pegreg.interpreters.TestPrintFst")
local luaunit = require("luaunit")
local pegreg = require("pegreg")

local nfa_to_dfa = pegreg.nfa_to_dfa
local l = pegreg.language
local expand_ref = pegreg.expand_ref
local expand_string = pegreg.expand_string
local add_left_right = pegreg.add_left_right
local mark_fin = pegreg.mark_fin
local enumerate = pegreg.enumerate
local state_arrow = pegreg.state_arrow
local flatten = pegreg.flatten
local reify = pegreg.reify

TestReify = {}

function TestReify.make_reified()
   local l = l.l()
   local reified = l:rule('A'):is(l:lit('aa'))
      :rule('B'):is(l:lit('bb'))
      :rule('K'):is(l:lit('x'))
      :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
      :create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(state_arrow)(flatten)(reify)
   return reified
end

function TestReify:testReifyOutput()
   print()
   print("Testing the reify interpreter")
   print(tostring(TestReify.make_reified()))
   -- TODO better tests here
end

function TestReify:testReifyInterpreter()
   TestPrintFst:assertSLInterpreter(reify)
end

function TestReify:testStateEq()
   local state1 = reify.state(1)[1]
   local state2 = reify.state(2)[1]
   luaunit.assertNotEquals(state1, state2)
   local state3 = reify.state(1)[1]
   luaunit.assertEquals(state1, state3)
end

function TestReify:testArrowEq()
   local arrow1 = reify.arrow(1, 2, 'a', 'a')[1]
   local arrow2 = reify.arrow(1, 3, 'a', 'a')[1]
   luaunit.assertNotEquals(arrow1, arrow2)
end

function TestReify:testStateLt()
   local state1 = reify.state(1)[1]
   local state2 = reify.state(2)[1]
   luaunit.assertTrue(state1 < state2, "1 < 2")
   luaunit.assertFalse(state2 < state1, "2 is not strictly less than 1")
   luaunit.assertFalse(state1 < state1, "1 is not strictly less than 1")
end

function TestReify:testArrowLt()
   local arrow1 = reify.arrow(1, 2, 'a', 'a')[1]
   local arrow2 = reify.arrow(1, 3, 'a', 'a')[1]
   luaunit.assertTrue(arrow1 < arrow2, "2 < 3")
   luaunit.assertFalse(arrow2 < arrow1, "3 is not stictly less than 2")
   luaunit.assertFalse(arrow1 < arrow1, "1, 2 is not strictly less than 1, 3")
   local arrow3 = reify.arrow(2, 1, 'a', 'a')[1]
   luaunit.assertTrue(arrow1 < arrow3, "1 < 2")
   luaunit.assertTrue(arrow2 < arrow3, "1 < 2")
end

function TestReify:testStateLte()
   local state1 = reify.state(1)[1]
   local state2 = reify.state(2)[1]
   luaunit.assertTrue(state1 <= state2, "1 <= 2")
   luaunit.assertFalse(state2 <= state1, "2 is not less than or equal to 1")
   luaunit.assertTrue(state1 <= state1, "1 is less than or equal to 1")
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

function TestReify:testDfstRejoining()
   local nfa = make_rejoining_nfst()
   local dfa = nfa_to_dfa.decorate(nfa_to_dfa.determinize(nfa))

   luaunit.assertEquals(dfa:size(), 4)
   local states = {}
   for state in dfa:states() do
      table.insert(states, state:number())
   end

   local arrows = {}
   for arrow in dfa:arrows() do
      table.insert(arrows, {arrow:from():number(),
                            arrow:to():number(),
                            arrow:input()})
   end

   luaunit.assertEquals(states, {0, 1, 2, 3})
   local arrow_expected = {
      {0, 1, "a"},
      {0, 2, "b"},
      {2, 3, "x"},
      {1, 3, "x"}
   }
   luaunit.assertEquals(arrows, arrow_expected)
end

-- NFST with branching and rejoining
-- States: 0, 1, 2
-- Final states: 2
-- Transitions:
-- from | to | tape
-- 0    | 1  | 0:0
-- 1    | 1  | a:a
-- 1    | 2  | a:a
local function make_astara()
   local p = reify.pair
   local s = reify.state
   local a = reify.arrow
   local states = reify.null()
   local arrows = reify.null()
   for i = 0, 1 do
      states = reify.pair(s(i, false), states)
   end
   states = p(s(2, true), states)
   arrows = p(a(0, 1, '', ''), arrows)
   arrows = p(a(1, 1, 'a', 'a'), arrows)
   arrows = p(a(1, 2, 'a', 'a'), arrows)
   return reify.create(states, arrows)
end

function TestReify:testReifiedToNFA()
   local nfa = make_astara()
   luaunit.assertEquals(nfa:start():number(), 0)
   luaunit.assertEquals(nfa:start():final(), false)
   luaunit.assertEquals(tostring(nfa:start().state), "(state 0 false)")
   local state_it = nfa:states()
   do
      local state = state_it()
      luaunit.assertEquals(state:number(), 0)
      luaunit.assertEquals(state:final(), false)
      luaunit.assertEquals(tostring(state.state), "(state 0 false)")
   end
   do
      local state = state_it()
      luaunit.assertEquals(state:number(), 1)
      luaunit.assertEquals(state:final(), false)
      luaunit.assertEquals(tostring(state.state), "(state 1 false)")
   end
   do
      local state = state_it()
      luaunit.assertEquals(state:number(), 2)
      luaunit.assertEquals(state:final(), true)
      luaunit.assertEquals(tostring(state.state), "(state 2 true)")
   end
   luaunit.assertEquals(state_it(), nil)
   local arrow_it = nfa:arrows()
   do
      local arrow = arrow_it()
      luaunit.assertEquals(arrow:from():number(), 0)
      luaunit.assertEquals(arrow:to():number(), 1)
      luaunit.assertEquals(arrow:input(), '')
   end
   do
      local arrow = arrow_it()
      luaunit.assertEquals(arrow:from():number(), 1)
      luaunit.assertEquals(arrow:to():number(), 1)
      luaunit.assertEquals(arrow:input(), 'a')
   end
   do
      local arrow = arrow_it()
      luaunit.assertEquals(arrow:from():number(), 1)
      luaunit.assertEquals(arrow:to():number(), 2)
      luaunit.assertEquals(arrow:input(), 'a')
   end
   luaunit.assertEquals(arrow_it(), nil)
end

function TestReify:testAStarA()
   print("Testing nfst->dfst states (a*)a")
   local l = l.l()
   local nfa = l:grammar(l:seq(l:star(l:lit('a')), l:lit('a')))
      :create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(state_arrow)(flatten)(reify)
   local dfa = nfa_to_dfa.decorate(nfa_to_dfa.determinize(nfa))

   luaunit.assertEquals(dfa:size(), 2)
   luaunit.assertEquals(dfa:start():number(), 0)
   local arrow_it = dfa:outgoing(dfa:start())
   local fst_arrow = arrow_it()
   luaunit.assertEquals(fst_arrow:from():number(), 0)
   luaunit.assertEquals(fst_arrow:to():number(), 1)
   luaunit.assertEquals(fst_arrow:input(), 'a')
   local snd_arrow = arrow_it()
   luaunit.assertEquals(snd_arrow, nil)

   local snd_state = fst_arrow:to()
   luaunit.assertEquals(snd_state:number(), 1)
   local snd_arrow_it = dfa:outgoing(snd_state)
   local snd_state_fst_arrow = snd_arrow_it()
   luaunit.assertEquals(snd_state_fst_arrow:from():number(), 1)
   luaunit.assertEquals(snd_state_fst_arrow:to():number(), 1)
   luaunit.assertEquals(snd_state_fst_arrow:input(), 'a')
   luaunit.assertEquals(snd_arrow_it(), nil)
end
