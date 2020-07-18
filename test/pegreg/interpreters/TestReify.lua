require("test.pegreg.interpreters.TestCreateArrows")
require("test.pegreg.interpreters.TestPrintFst")
local luaunit = require("luaunit")
local pegreg = require("pegreg")

local l = pegreg.language
local expand_ref = pegreg.expand_ref
local expand_string = pegreg.expand_string
local add_left_right = pegreg.add_left_right
local mark_fin = pegreg.mark_fin
local enumerate = pegreg.enumerate
local state_arrow = pegreg.state_arrow
local flatten = pegreg.flatten
local reify2 = pegreg.reify2

local data_structures = require("pegreg.data_structures")

TestReify = {}

function TestReify.make_reified()
   local l = l.l()
   local reified = l:rule('A'):is(l:lit('aa'))
      :rule('B'):is(l:lit('bb'))
      :rule('K'):is(l:lit('x'))
      :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
      :create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(state_arrow)(flatten)(reify2)
   return reified
end

function TestReify:testReifyOutput()
   print()
   print("Testing the reify interpreter")
   print(tostring(TestReify.make_reified()))
end

function TestReify:testReifyInterpreter()
   TestPrintFst:assertSLInterpreter(reify2)
end

function TestReify:testStateEq()
   local state1 = reify2.state(1):get(1)
   local state2 = reify2.state(2):get(1)
   luaunit.assertNotEquals(state1, state2)
   local state3 = reify2.state(1):get(1)
   luaunit.assertEquals(state1, state3)
end

function TestReify:testArrowEq()
   local arrow1 = reify2.arrow(1, 2, 'a', 'a'):get(1)
   local arrow2 = reify2.arrow(1, 3, 'a', 'a'):get(1)
   luaunit.assertNotEquals(arrow1, arrow2)
end

function TestReify:testStateLt()
   local state1 = reify2.state(1):get(1)
   local state2 = reify2.state(2):get(1)
   luaunit.assertTrue(state1 < state2, "1 < 2")
   luaunit.assertFalse(state2 < state1, "2 is not strictly less than 1")
   luaunit.assertFalse(state1 < state1, "1 is not strictly less than 1")
end

function TestReify:testArrowLt()
   local arrow1 = reify2.arrow(1, 2, 'a', 'a'):get(1)
   local arrow2 = reify2.arrow(1, 3, 'a', 'a'):get(1)
   luaunit.assertTrue(arrow1 < arrow2, "2 < 3")
   luaunit.assertFalse(arrow2 < arrow1, "3 is not stictly less than 2")
   luaunit.assertFalse(arrow1 < arrow1, "1, 2 is not strictly less than 1, 3")
   local arrow3 = reify2.arrow(2, 1, 'a', 'a'):get(1)
   luaunit.assertTrue(arrow1 < arrow3, "1 < 2")
   luaunit.assertTrue(arrow2 < arrow3, "1 < 2")
end

function TestReify:testStateLte()
   local state1 = reify2.state(1):get(1)
   local state2 = reify2.state(2):get(1)
   luaunit.assertTrue(state1 <= state2, "1 <= 2")
   luaunit.assertFalse(state2 <= state1, "2 is not less than or equal to 1")
   luaunit.assertTrue(state1 <= state1, "1 is less than or equal to 1")
end
