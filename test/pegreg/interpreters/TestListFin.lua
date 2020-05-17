require("test.pegreg.interpreters.TestEnumerate")

local pegreg = require("pegreg")

local l = pegreg.language
local expand_ref = pegreg.expand_ref
local expand_string = pegreg.expand_string
local mark_fin = pegreg.mark_fin
local enumerate = pegreg.enumerate
local remark_fin = pegreg.remark_fin
local list_fin = pegreg.list_fin

TestListFin = {}

function TestListFin:testListFin()

   do
      print()
      print("Testing the list finstates interpreter")
      local l = l.l()
      local states = l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('A')))
         :create(expand_ref)(expand_string)(mark_fin)(enumerate)(remark_fin)(list_fin)
      for i, v in ipairs(states) do
         print(i, v)
      end
   end
end

function TestListFin:testListFinInterpreter()
   TestEnumerate:assertNInterpreter(list_fin)
end
