local pegreg = require("pegreg")
local luaunit = require("luaunit")

local compiler = pegreg.compiler

TestCompiler = {}

function TestCompiler:testCompilerOutput()
      local l = compiler.l()
      local it = l:rule('A'):is(l:lit('aa'))
                  :rule('B'):is(l:lit('bb'))
                  :rule('K'):is(l:lit('x'))
                  :grammar(l:seq(l:choice(l:ref('A'), l:ref('B')), l:ref('K')))
                  :create()
      local outstr, match_success, matched_states = it:match_string("bbx")
      luaunit.assertEquals(outstr, "bbx")
      luaunit.assertTrue(match_success)
      luaunit.assertEquals(matched_states, {2, 3, 4})

end

