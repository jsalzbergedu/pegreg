require("test.pegreg.interpreters.TestPrintSyntax")

local luaunit = require("luaunit")
local pegreg = require("pegreg")

local expand_ref = pegreg.expand_ref
local expand_string = pegreg.expand_string
local print_syntax = pegreg.print_syntax
local l = pegreg.language

TestExpandRef = {}

function TestExpandRef:testExpandRef()
   ----------------------------------------------------------------------------
   -- Test the expand ref interpreter
   ---------------------------------------------------------------------------
   print()
   print("Testing the expand ref interpreter")
   do
      local l = l.l()
      l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
         :create(expand_ref)(expand_string)(print_syntax)
   end
end

function TestExpandRef:testExpandRefInterpreter()
   TestPrintSyntax:assertPegregInterpreter(expand_ref)
end
