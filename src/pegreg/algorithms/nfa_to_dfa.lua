local nfa_to_dfa = {}
local array = require("pegreg.util.array")
local make_it = array.make_it

-- NFA expected interface:
-- Base types: State, Arrow
-- Composite type: NFA
-- State has the following methods
--   state:number() get the states number
--   state:final() get whether the state is final
--   state:contains(substate) return whether the state contains the substate
--   state:substates() return an iterator over the substates of the state
-- Arrow has the following methods
--   arrow:from() gets the State that it is from
--   arrow:to() gets the State that it is to
--   arrow:input() gets the input character
-- NFA has the following methods
--   nfa:outgoing(state)
--     get all of the outgoing arrows of the
--     nfa at state.
--   nfa:states()
--     get all the states as an iterator over States
--   nfa:size()
--     get the number of states in the nfa
--   nfa:arrows()
--     get all the arrows as an iterator over Arrows
--   nfa:start()
--     get the start state of the nfa
-- These are all abstract interfaces,
-- and not actual implemented things.

--------------------------------------------------------------------------------
-- Given an abstract nfa, NFA,
-- a state, STATE, and an empty table,
-- ECLOSURE, store the epsilon closure
-- of the STATE in the ECLOSURE.
--------------------------------------------------------------------------------
function nfa_to_dfa.eclose_rec(nfa, state, eclosure)
   table.insert(eclosure, state)
   for arrow in nfa:outgoing(state) do
      if arrow:input() == '' then
         nfa_to_dfa.eclose_rec(nfa, arrow:to(), eclosure)
      end
   end
end

--------------------------------------------------------------------------------
-- Given two states,
-- STATE1 and STATE2,
-- return whether state1 is less than state2
--------------------------------------------------------------------------------
local function state_lt(state1, state2)
   return state1:number() < state2:number()
end

--------------------------------------------------------------------------------
-- Given an abstract nfa, NFA,
-- a state, STATE, and an empty table,
-- return a sorted list of states
-- that form its STATE's epsilon closure
--------------------------------------------------------------------------------
function nfa_to_dfa.eclose(nfa, state)
   local eclosure = {}
   nfa_to_dfa.eclose_rec(nfa, state, eclosure)
   table.sort(eclosure, state_lt)
   return eclosure
end

--------------------------------------------------------------------------------
-- Given SET1 and SET2,
-- both lua arrays of states,
-- return whether they are the same lua array of states
--------------------------------------------------------------------------------
local function state_set_equal(set1, set2)
   if #set1 ~= #set2 then
      return false
   end
   for i = 1, #set1, 1 do
      if set1[i]:number() ~= set2[i]:number() then
         return false
      end
   end
   return true
end

--------------------------------------------------------------------------------
-- Given SUPERSTATES and ITEM,
-- a lua array of lua arrays of states,
-- and ITEM, a lua array of states,
-- return the index of ITEM if it
-- exists in SUPERSTATES and -1 if it does not.
--------------------------------------------------------------------------------
local function superstate_set_indexof(superstates, item)
   local out = -1
   for i, set in ipairs(superstates) do
      if state_set_equal(set, item) then
         out = i
      end
   end
   return out
end

--------------------------------------------------------------------------------
-- Given SUPERSTATES and ITEM,
-- a lua array of lua arrays and a
-- lua array of states,
-- check if ITEM is in superstates.
-- if it is not, add it to superstates.
-- Returns the index of ITEM in superstates.
--------------------------------------------------------------------------------
local function superstate_add(superstates, item)
   local index = superstate_set_indexof(superstates, item)
   if index == -1 then
      index = #superstates + 1
      superstates[index] = item
   end
   return index
end

--------------------------------------------------------------------------------
-- Using NFA,
-- find all of the outgoing states of SET,
-- a lua array of states,
-- and return them as a map of input
-- characters to a map of state
-- numbers to states.
--------------------------------------------------------------------------------
function nfa_to_dfa.outgoing_of_set(nfa, set)
   local outstates_by_character = {}
   for _, state in ipairs(set) do
      for arrow in nfa:outgoing(state) do
         local eclosure = nfa_to_dfa.eclose(nfa, arrow:to())
         if outstates_by_character[arrow:input()] == nil then
            if arrow:input() ~= '' then
               outstates_by_character[arrow:input()] = {}
            end
         end
         for _, substate in ipairs(eclosure) do
            if arrow:input() ~= '' then
               outstates_by_character[arrow:input()][substate:number()] = substate
            end
         end
      end
   end
   return outstates_by_character
end

--------------------------------------------------------------------------------
-- Take the abstract nfa, NFA,
-- and return two arrays,
-- arrows and superstates.
-- arrows is formatted like so:
-- {ARROW, ARROW, ...}
-- where ARROW is a triplet, {FROM, TO, INPUT},
-- FROM being the superstate its from, TO being the
-- superstate its to, and INPUT being the input character.
-- superstates is formatted like so:
-- {SUPERSTATE, SUPERSTATE, ...}
-- where each SUPERSTATE is a subset of the nfa's states.
--------------------------------------------------------------------------------
function nfa_to_dfa.determinize(nfa)
   local list_of_superstates = {}
   local starting_point = nfa_to_dfa.eclose(nfa, nfa:start())
   table.insert(list_of_superstates, starting_point)

   local new_arrows = {}

   local state_set_stack = {}
   table.insert(state_set_stack, {1, starting_point})
   while #state_set_stack > 0 do
      -- Pop the stack
      local i, set = table.unpack(state_set_stack[#state_set_stack])
      state_set_stack[#state_set_stack] = nil

      local outstates_by_character = nfa_to_dfa.outgoing_of_set(nfa, set)

      local outstate_character_list = {}
      for k, v in pairs(outstates_by_character) do
         local outstate_list = {}
         for _, state in pairs(v) do
            table.insert(outstate_list, state)
         end
         table.sort(outstate_list, state_lt)
         local char_and_states = {}
         char_and_states.k = k
         char_and_states.outstate_list = outstate_list
         table.insert(outstate_character_list, char_and_states)
      end
      table.sort(outstate_character_list, function (a, b) return a.k < b.k end)

      for _, char_and_states in ipairs(outstate_character_list) do
         local outstate_list = char_and_states.outstate_list
         local new_state = false
         if superstate_set_indexof(list_of_superstates, outstate_list) == -1 then
            new_state = true
         end
         local sublist_index = superstate_add(list_of_superstates, outstate_list)
         if new_state then
            table.insert(state_set_stack, {sublist_index, outstate_list})
         end
         table.insert(new_arrows, {i - 1, sublist_index - 1, char_and_states.k})
      end
   end
   return list_of_superstates, new_arrows
end

--------------------------------------------------------------------------------
-- Given a LIST_OF_SUPERSTATES and NEW_ARROWS,
-- return a DFA with the interface of an NFA.
--------------------------------------------------------------------------------
function nfa_to_dfa.decorate(list_of_superstates, new_arrows)
   local number_to_state = {}
   for i, superstate in ipairs(list_of_superstates) do
      local number = i - 1
      local state_impl = {}
      function state_impl:number()
         return number
      end
      local one_true = false
      for _, state in ipairs(superstate) do
         one_true = state:final() or one_true
      end
      function state_impl:final()
         return one_true
      end

      function state_impl:contains(substate)
         for _, state in ipairs(superstate) do
            if substate:number() == state:number() then
               return true
            end
         end
         return false
      end

      function state_impl:substates()
         return make_it(superstate)
      end

      superstate = setmetatable(superstate, {__index = state_impl})
      number_to_state[superstate:number()] = superstate
   end

   for _, arrow in ipairs(new_arrows) do
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

   local outgoings_by_state = {}
   for _, superstate in ipairs(list_of_superstates) do
      local outgoings = {}
      outgoings_by_state[superstate:number()] = outgoings
      for _, arrow in ipairs(new_arrows) do
         if arrow:from():number() == superstate:number() then
            table.insert(outgoings, arrow)
         end
      end
      table.sort(outgoings,
                 function (a1, a2)
                    return a1:input() < a2:input()
                 end)
   end

   function nfa_impl:outgoing(state)
      assert(outgoings_by_state[state:number()],
             tostring(state:number()) .. " not in nfa.")
      local outgoings = outgoings_by_state[state:number()]
      return make_it(outgoings)
   end

   function nfa_impl:states()
      return make_it(list_of_superstates)
   end

   function nfa_impl:arrows()
      return make_it(new_arrows)
   end

   function nfa_impl:start()
      return list_of_superstates[1]
   end

   function nfa_impl:size()
      return #list_of_superstates
   end

   return setmetatable({list_of_superstates, new_arrows}, {__index = nfa_impl})
end

return nfa_to_dfa
