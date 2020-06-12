require("test.pegreg.interpreters.TestEnumerate")

local pegreg = require("pegreg")
local l = pegreg.language
local expand_ref = pegreg.expand_ref
local expand_string = pegreg.expand_string
local mark_fin = pegreg.mark_fin
local enumerate = pegreg.enumerate
local create_states = pegreg.create_states
local flatten = pegreg.flatten
local print_fst = pegreg.print_fst

TestCreateStates = {}

function TestCreateStates:testCreateStateOutput()
   --------------------------------------------------------------------------------
   -- Test the create states interpreter
   --------------------------------------------------------------------------------
   print()
   print("Testing the create states interpreter")
   do
      local interpreter = expand_string.create()
      local l = l.l(interpreter)
      l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('A')))
         :create(expand_ref)(expand_string)(mark_fin)(enumerate)(create_states)(flatten)(print_fst)
   end
end


function TestCreateStates:testCreateStatesInterpreter()
   TestEnumerate:assertNInterpreter(create_states)
end
