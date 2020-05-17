require("test.pegreg.interpreters.TestPrintSyntax")

local luaunit = require("luaunit")
local pegreg = require("pegreg")
local l = pegreg.language
local add_left_right = pegreg.add_left_right
local expand_string = pegreg.expand_string
local expand_ref = pegreg.expand_ref
local print_lr = pegreg.print_lr

TestAddLeftRight = {}

function TestAddLeftRight:testLROutput()
   print()
   print("Testing the left right interpreter")
   do
      local l = l.l()
      l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
         :create(expand_ref)(expand_string)(add_left_right)(print_lr)
   end
end

--------------------------------------------------------------------------------
-- Ensures that the interpreter has PEGREG extended with left_right
--------------------------------------------------------------------------------
function TestAddLeftRight:assertLRInterpreter(interpreter)
   TestPrintSyntax:assertPegregInterpreter(interpreter)
   luaunit.assertEquals(type(interpreter.left), "function", "No left")
   luaunit.assertEquals(type(interpreter.right), "function", "No right")
end

function TestAddLeftRight:testAddLRInterpreter()
   TestPrintSyntax:assertPegregInterpreter(add_left_right)
end

function TestAddLeftRight:testPrintLrInterpreter()
   TestAddLeftRight:assertLRInterpreter(print_lr)
end
