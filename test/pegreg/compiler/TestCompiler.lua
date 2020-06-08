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
      luaunit.assertEquals(matched_states, {2, 4, 5})
end

function TestCompiler:testCompilerOutput2()
      local l = compiler.l()
      local it = l:grammar(l:seq(l:choice(l:lit('Jamie'), l:lit('A')), l:lit('Jennings')))
                  :create()
      local outstr, match_success, matched_states = it:match_string("AJennings")
      luaunit.assertEquals(outstr, "AJennings")
      luaunit.assertTrue(match_success)
      luaunit.assertEquals(matched_states, {1, 3, 5, 7, 9, 11, 12, 13, 14})

      local outstr, match_success, matched_states = it:match_string("JamieJennings")
      luaunit.assertEquals(outstr, "JamieJennings")
      luaunit.assertTrue(match_success)
      luaunit.assertEquals(matched_states, {2, 4, 6, 8, 10, 3, 5, 7, 9, 11, 12, 13, 14})
end
