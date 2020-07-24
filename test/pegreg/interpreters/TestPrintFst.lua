local pegreg = require("pegreg")
local luaunit = require("luaunit")

local fstl = pegreg.fst_language
local print_nfa = pegreg.print_nfa

TestPrintFst = {}

function TestPrintFst:testPrintFstOutput()
   do
      local l = fstl.l()

      l:state(0, false)
         :state(1, false)
         :state(2, true)
         :arrow(0, 1, 'a', 'a')
         :arrow(1, 2, 'b', 'b')
         :create(print_nfa)
   end
end

--------------------------------------------------------------------------------
-- Assert that the state interpreter has all the functions required
--------------------------------------------------------------------------------
function TestPrintFst:assertSLInterpreter(interpreter)
   luaunit.assertEquals(type(interpreter.state), "function", "No State")
   luaunit.assertEquals(type(interpreter.arrow), "function", "No Arrow")
   luaunit.assertEquals(type(interpreter.pair), "function", "No Pair")
   luaunit.assertEquals(type(interpreter.null), "function", "No Null")
   luaunit.assertEquals(type(interpreter.create), "function", "No Create")
end

function TestPrintFst:testPrintFstInterpreter()
   TestPrintFst:assertSLInterpreter(print_nfa)
end
