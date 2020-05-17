local luaunit = require("luaunit")
local pegreg = require("pegreg")
local print_syntax = pegreg.print_syntax
local l = pegreg.language

TestPrintSyntax = {}

function TestPrintSyntax:testPrintSyntaxOutput()
   print("Testing the print syntax interpreter")
   do
      local l = l.l()
      l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
         :create(print_syntax)
   end
end

--------------------------------------------------------------------------------
-- A method to assert that the interpreter can interpret
-- the PEGREG dsl in its entirety
--------------------------------------------------------------------------------
function TestPrintSyntax:assertPegregInterpreter(interpreter)
   local must_have = {
      "e",
      "lit",
      "seq",
      "choice",
      "grammar",
      "ref",
      "create",
      "star"
   }
   for _, v in ipairs(must_have) do
      if type(interpreter[v]) ~= "function" then
         luaunit.fail("No " .. v)
      end
   end
end


function TestPrintSyntax:testPegregInterpreter()
   TestPrintSyntax:assertPegregInterpreter(print_syntax)
end
