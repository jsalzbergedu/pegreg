local pegreg = require("pegreg")
local nfa_to_dfa = pegreg.nfa_to_dfa
local luaunit = require("luaunit")

TestNFAToDFA = {}

--------------------------------------------------------------------------------
-- Make an iterator on the array arr
--------------------------------------------------------------------------------
local function make_it(arr)
   local idx = 1
   local function it()
      if idx <= #arr then
         local out = arr[idx]
         idx = idx + 1
         return out
      else
         return nil
      end
   end
   return it
end

--------------------------------------------------------------------------------
-- Take an NFA of the form
-- {STATES, ARROWS}
-- where STATES are in the format
-- {{0, false}, {1, false}, {2, false}, ...}
-- and ARROWS are in the format
-- {{0, 1, 'a'}, {1, 2, 'b'}, {3, 4, ''}, ...}
-- and return an abstracted NFA.
--------------------------------------------------------------------------------
function TestNFAToDFA:abstract_from_basic(nfa)
   local number_to_state = {}
   for _, state in ipairs(nfa[1]) do
      local state_impl = {}
      function state_impl:number()
         return state[1]
      end
      function state_impl:final()
         return state[2]
      end
      state = setmetatable(state, {__index = state_impl})
      number_to_state[state:number()] = state
   end

   for _, arrow in ipairs(nfa[2]) do
      local arrow_impl = {}
      function arrow_impl:from()
         return number_to_state[arrow[1]]
      end
      function arrow_impl:to()
         return number_to_state[arrow[2]]
      end
      function arrow_impl:input()
         return arrow[3]
      end
      arrow = setmetatable(arrow, {__index = arrow_impl})
   end

   local nfa_impl = {}
   function nfa_impl:outgoing(state)
      local outgoings = {}
      for _, arrow in ipairs(nfa[2]) do
         if arrow:from():number() == state:number() then
            table.insert(outgoings, arrow)
         end
      end
      table.sort(outgoings, function (a1, a2)
                    return a1:to():number() < a2:to():number()
      end)
      local idx = 1
      local function it()
         if idx <= #outgoings then
            local out = outgoings[idx]
            idx = idx + 1
            return out
         else
            return nil
         end
      end
      return it
   end

   function nfa_impl:states()
      return make_it(nfa[1])
   end

   function nfa_impl:size()
      return #nfa[1]
   end

   function nfa_impl:arrows()
      return make_it(nfa[2])
   end

   function nfa_impl:start()
      return nfa[1][1]
   end

   nfa = setmetatable(nfa, {__index = nfa_impl})
   return nfa
end

local astara = {
   {{0, false}, {1, false}, {2, true}},
   {{0, 1, ''}, {1, 1, 'a'}, {1, 2, 'a'}}
}

local abstract = TestNFAToDFA:abstract_from_basic(astara)


function TestNFAToDFA:testDeterminize()
   local states, arrows = nfa_to_dfa.determinize(abstract)
   luaunit.assertEquals(states[1], {{0, false}, {1, false}})
   luaunit.assertEquals(states[2], {{1, false}, {2, true}})
   luaunit.assertEquals(#states, 2)

   luaunit.assertEquals(arrows[1], {0, 1, 'a'})
   luaunit.assertEquals(arrows[2], {1, 1, 'a'})
end

function TestNFAToDFA:testDecorate()
   local states, arrows = nfa_to_dfa.determinize(abstract)
   local dfa = nfa_to_dfa.decorate(states, arrows)
   luaunit.assertEquals(dfa:start(), {{0, false}, {1, false}})
   do
      local it = dfa:outgoing(dfa:start())
      luaunit.assertEquals(it(), {0, 1, 'a'})
      luaunit.assertEquals(it(), nil)
   end
   do
      local it = dfa:outgoing(dfa:outgoing(dfa:start())():to())
      local arrow = it()
      luaunit.assertEquals(arrow, {1, 1, 'a'})
      luaunit.assertEquals(arrow:to(), {{1, false}, {2, true}})
      luaunit.assertEquals(it(), nil)
   end
   do
      local it = dfa:states()
      local state1 = it()
      luaunit.assertEquals(state1, {{0, false}, {1, false}})
      luaunit.assertFalse(state1:final())
      local state2 = it()
      luaunit.assertEquals(state2, {{1, false}, {2, true}})
      luaunit.assertTrue(state2:final())
      luaunit.assertEquals(it(), nil)
   end
   do
      local it = dfa:arrows()
      local arrow1 = it()
      luaunit.assertEquals(arrow1, {0, 1, 'a'})
      luaunit.assertEquals(arrow1:from(), {{0, false}, {1, false}})
      luaunit.assertEquals(arrow1:to(), {{1, false}, {2, true}})
      luaunit.assertEquals(arrow1:input(), 'a')
      local arrow2 = it()
      luaunit.assertEquals(arrow2, {1, 1, 'a'})
      luaunit.assertEquals(arrow2:from(), {{1, false}, {2, true}})
      luaunit.assertEquals(arrow2:to(), {{1, false}, {2, true}})
      luaunit.assertEquals(arrow2:input(), 'a')
   end
end
