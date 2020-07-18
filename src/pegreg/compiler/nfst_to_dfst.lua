local data_structures = require("pegreg.data_structures")
local list = data_structures.list

local nfst_to_dfst = {}

function nfst_to_dfst.sort_reified(reified)
   list.sort(reified.states)
   list.sort(reified.arrows)
end

local function nub(lst)
   local out = list.new()
   if #lst > 0 then
      local prev = lst:get(1)
      list.insert(out, lst:get(1))
      for i = 2, #lst, 1 do
         if prev ~= lst:get(i) then
            list.insert(out, lst:get(i))
         end
         prev = lst:get(i)
      end
   end
   return out
end

function nfst_to_dfst.nub(reified)
   nfst_to_dfst.sort_reified(reified)
   reified.states = nub(reified.states)
   reified.arrows = nub(reified.arrows)
   return reified
end

--------------------------------------------------------------------------------
-- Given an array, make an iterator over it
-- TODO move this to a utility file
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
-- TODO Move this as well
--------------------------------------------------------------------------------
local function make_list_it(lst)
   local idx = 1
   local function it()
      if idx <= #lst then
         local out = lst:get(idx)
         idx = idx + 1
         return out
      else
         return nil
      end
   end
   return it
end

--------------------------------------------------------------------------------
-- Take REIFIED, a reified set of states and arrows,
-- and create something that conforms to the
-- NFA interface defined in the file
-- nfa_to_dfa.lua
--------------------------------------------------------------------------------
function nfst_to_dfst.reified_to_nfa(reified)
   -- First, nub and sort
   nfst_to_dfst.nub(reified)

   -- Now, make wrappers for all of the states
   local state_to_state_wrapper = {}
   local state_to_arrows = {}
   for _, state in ipairs(reified.states) do
      local state_wrapper = {state = state}
      state_to_state_wrapper[state.number] = state_wrapper
      state_to_arrows[state.number] = {}

      function state_wrapper:number()
         return self.state.number
      end

      function state_wrapper:final()
         return self.state.final
      end

      function state_wrapper:contains()
         return false
      end

      function state_wrapper:substates()
         return function ()
            return nil
         end
      end

      for _, arrow in ipairs(reified.arrows) do
         if arrow.from == state.number then
            table.insert(state_to_arrows[state.number], arrow)
         end
         -- Sort to make the order of the arrows
         -- deterministic
         table.sort(state_to_arrows[state.number],
                    function (a, b)
                       return a.to < b.to
                    end)
      end
   end

   -- Now, make wrappers for all the arrows
   local arrow_to_arrow_wrapper = {}
   for _, arrow in ipairs(reified.arrows) do
      local arrow_wrapper = {arrow = arrow}
      arrow_to_arrow_wrapper[arrow] = arrow_wrapper

      function arrow_wrapper:from()
         return state_to_state_wrapper[self.arrow.from]
      end

      function arrow_wrapper:to()
         return state_to_state_wrapper[self.arrow.to]
      end

      function arrow_wrapper:input()
         return self.arrow.input
      end

      -- TODO For now this library will not expose
      -- the arrow's output.
      -- not sure the implications,
      -- but preferably the output should be
      -- exposed.
   end

   -- Map states to arrow wrappers
   local state_to_arrow_wrapper = {}
   for _, state in ipairs(reified.states) do
      local wrappers = {}
      state_to_arrow_wrapper[state.number] = wrappers
      for _, arrow in ipairs(state_to_arrows[state.number]) do
         table.insert(wrappers, arrow_to_arrow_wrapper[arrow])
      end
   end

   -- Finally, wrap the whole NFA
   local nfa = {}
   function nfa:outgoing(state)
      return make_it(state_to_arrow_wrapper[state:number()])
   end

   function nfa:states()
      local it = make_list_it(reified.states)
      local function wrapper()
         local v = it()
         return v and state_to_state_wrapper[v.number]
      end
      return wrapper
   end

   function nfa:size()
      return #reified.states
   end

   function nfa:arrows()
      local it = make_list_it(reified.arrows)
      local function wrapper()
         local v = it()
         return v and arrow_to_arrow_wrapper[v]
      end
      return wrapper
   end

   function nfa:start()
      return state_to_state_wrapper[reified.states:get(1).number]
   end

   return nfa
end

return nfst_to_dfst
