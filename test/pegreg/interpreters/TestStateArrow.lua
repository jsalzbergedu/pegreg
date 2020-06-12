require("test.pegreg.interpreters.TestCreateArrows")
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
local print_n = pegreg.print_n
local print_fst = pegreg.print_fst

TestStateArrow = {}

function TestStateArrow:testStateArrowOutput()
   print()
   print("Testing the create states and arrow interpreter")
   print("From:")
   do
      local l = l.l()
      local arrows = l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
         :create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(print_n)
   end
   print("To:")
   do
      local l = l.l()
      local arrows = l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
         :create(expand_ref)(expand_string)(add_left_right)(mark_fin)(enumerate)(state_arrow)(flatten)(print_fst)
   end
end

function TestCreateArrows:testStateArrowStar()
   print()
   print("Testing the state_arrow interpreter w/ star")
   do
      local l = l.l()
      local arrows = l:grammar(l:seq(l:star(l:lit("a")), l:lit("b")))
         :create(expand_ref)(expand_string)(mark_fin)(enumerate)(state_arrow)(flatten)(print_fst)
   end
end

function TestStateArrow:testStateArrowInterpreter()
   TestEnumerate:assertNInterpreter(state_arrow)
end
