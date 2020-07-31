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

function TestCompiler:testCompilerOutput2()
      local l = compiler.l()
      local it = l:grammar(l:seq(l:choice(l:lit('Jamie'), l:lit('A')), l:lit('Jennings')))
                  :create()
      local outstr, match_success, matched_states = it:match_string("AJennings")
      luaunit.assertEquals(outstr, "AJennings")
      luaunit.assertTrue(match_success)
      luaunit.assertEquals(matched_states, {1, 7, 8, 9, 10, 11, 12, 13, 14})

      local outstr, match_success, matched_states = it:match_string("JamieJennings")
      luaunit.assertEquals(outstr, "JamieJennings")
      luaunit.assertTrue(match_success)
      luaunit.assertEquals(matched_states, {2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14})
end

local very_large = [[
Jamie was raised, in a different time and place, by itinerant goat herders. Her childhood companions were small prairie mammals and dreams of computing machines.
]]

function TestCompiler:testCompilerOutput3()
      local l = compiler.l()
      local it = l:grammar(l:lit(very_large))
                  :create()
      local outstr, match_success, matched_states = it:match_string("Jamie")
      luaunit.assertEquals(outstr, "Jamie")
      luaunit.assertFalse(match_success)
      luaunit.assertEquals(matched_states, {1, 2, 3, 4, 5})

      local outstr, match_success, matched_states = it:match_string(very_large)
      luaunit.assertEquals(outstr, very_large)
      luaunit.assertTrue(match_success)
      luaunit.assertEquals(#matched_states, #very_large)
end

function TestCompiler:testCompilerStar()
   local l = compiler.l()
   local it = l:grammar(l:seq(l:star(l:lit('a')), l:lit('b'))):create()
   local outstr, match_success, matched_states = it:match_string("aaaab")
   luaunit.assertEquals(outstr, "aaaab")
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {1, 1, 1, 1, 2})
end


function TestCompiler:testStarNotPossesive()
   local l = compiler.l()
   local it = l:grammar(l:seq(l:star(l:lit('a')), l:lit('a'))):create()
   local outstr, match_success, matched_states = it:match_string("aa")
   luaunit.assertEquals(outstr, "aa")
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {1, 1})
end

function TestCompiler:testSingularChar()
   local l = compiler.l()
   local it = l:grammar(l:lit('a')):create()
   local outstr, match_success, matched_states = it:match_string('a')
   luaunit.assertEquals(outstr, 'a')
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {1})
end

function TestCompiler:testAStar()
   local l = compiler.l()
   local it = l:grammar(l:star(l:lit('a'))):create()
   local outstr, match_success, matched_states = it:match_string('aa')
   luaunit.assertEquals(outstr, 'aa')
   luaunit.assertTrue(match_success)
   luaunit.assertEquals(matched_states, {1, 1})
end
