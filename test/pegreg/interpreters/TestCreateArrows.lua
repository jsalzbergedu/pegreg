local pegreg = require("pegreg")
local l = pegreg.language
local expand_ref = pegreg.expand_ref
local expand_string = pegreg.expand_string
local mark_fin = pegreg.mark_fin
local enumerate = pegreg.enumerate
local create_arrows = pegreg.create_arrows
local flatten = pegreg.flatten
local print_fst = pegreg.print_fst

TestCreateArrows = {}

--------------------------------------------------------------------------------
-- Test the arrows interpreter
--------------------------------------------------------------------------------
function TestCreateArrows:testCreateArrows()
   print()
   print("Testing the create arrows interpreter")
   do
      local l = l.l()
      local arrows = l:rule('A'):is(l:lit('aa'))
         :rule('B'):is(l:lit('bb'))
         :rule('K'):is(l:lit('x'))
         :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
         :create(expand_ref)(expand_string)(mark_fin)(enumerate)(create_arrows)(flatten)(print_fst)
   end
end

function TestCreateArrows:testCreateArrowsStar()
   print()
   print("Testing the create arrows interpreter w/ star")
   do
      local l = l.l()
      local arrows = l:grammar(l:seq(l:star(l:lit("a")), l:lit("b")))
         :create(expand_ref)(expand_string)(mark_fin)(enumerate)(create_arrows)(flatten)(print_fst)
   end
end

function TestCreateArrows:testCreateNInterpreter()
   TestEnumerate:assertNInterpreter(create_arrows)
end
