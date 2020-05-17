require("test.pegreg.interpreters.TestPrintSyntax")
local pegreg = require("pegreg")

local l = pegreg.language
local expand_string = pegreg.expand_string
local print_syntax = pegreg.print_syntax

TestExpandString = {}

---------------------------------------------------------------------------
-- Test the expand string interpreter
---------------------------------------------------------------------------
function TestExpandString:testExpandString()
   print()
   print("Testing the expand string interpreter")
   do
      local l = l.l()
      l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
         :create(expand_string)(print_syntax)
   end
end

function TestExpandString:testExpandStringInterpreter()
   TestPrintSyntax:assertPegregInterpreter(expand_string)
end
