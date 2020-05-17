require("test.pegreg.interpreters.TestMarkFin")

local luaunit = require("luaunit")
local pegreg = require("pegreg")

local l = pegreg.language
local expand_ref = pegreg.expand_ref
local expand_string = pegreg.expand_string
local mark_fin = pegreg.mark_fin
local enumerate = pegreg.enumerate
local print_n = pegreg.print_n

TestEnumerate = {}

function TestEnumerate:testEnumerateOutput()
   ----------------------------------------------------------------------------
   -- Testing the enumerate interpreter
   ---------------------------------------------------------------------------
   print()
   print("Testing the enumerate interpreters")
   do
      local l = l.l()
      l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
         :create(expand_ref)(expand_string)(mark_fin)(enumerate)(print_n)
   end

   do
      local l = l.l()
      l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('A')))
         :create(expand_ref)(expand_string)(mark_fin)(enumerate)(print_n)
   end
end

--------------------------------------------------------------------------------
-- Assert that the interpreter can interpret
-- PEGREG extended to include fin and enumeration
--------------------------------------------------------------------------------
function TestEnumerate:assertNInterpreter(interpreter)
   TestMarkFin:assertFinInterpreter(interpreter)
   luaunit.assertEquals(type(interpreter.mark_n), "function", "No mark_n")
end

function TestEnumerate:testEnumerateInterpreter()
   self.TestMarkFin:assertFinInterpreter(enumerate)
end

function TestEnumerate:testPrintNInterpreter()
   TestEnumerate:assertNInterpreter(print_n)
end

function TestEnumerate:testEnumerateInterpreter()
   TestMarkFin:assertFinInterpreter(enumerate)
end
