require("test.pegreg.interpreters.TestPrintSyntax")
require("test.pegreg.interpreters.TestAddLeftRight")

local luaunit = require("luaunit")
local pegreg = require("pegreg")
local l = pegreg.language
local expand_ref = pegreg.expand_ref
local expand_string = pegreg.expand_string
local mark_fin = pegreg.mark_fin
local print_fin = pegreg.print_fin

TestMarkFin = {}

----------------------------------------------------------------------------
-- Test the fin print
---------------------------------------------------------------------------
function TestMarkFin:testMarkFinOutput()
   local l = pegreg.language
   local expand_ref = pegreg.expand_ref
   local expand_string = pegreg.expand_string
   local mark_fin = pegreg.mark_fin
   local print_fin = pegreg.print_fin

   print()
   print("Testing the mark final interpreters")
   do
      local l = l.l()
      l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
         :create(expand_ref)(expand_string)(mark_fin)(print_fin)
   end

   do
      local l = l.l()
      l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('A')))
         :create(expand_ref)(expand_string)(mark_fin)(print_fin)
   end
end

function TestMarkFin:assertFinInterpreter(interpreter)
   TestAddLeftRight:assertLRInterpreter(interpreter)
   luaunit.assertEquals(type(interpreter.fin), "function", "No fin")
   luaunit.assertEquals(type(interpreter.notfin), "function", "No notfin")
end

function TestMarkFin:testMarkfinInterpreter()
   TestPrintSyntax:assertPegregInterpreter(mark_fin)
end

function TestMarkFin:testPrintInterpreter()
   self:assertFinInterpreter(print_fin)
end
