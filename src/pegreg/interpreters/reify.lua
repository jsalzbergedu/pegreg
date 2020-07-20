local data_structures = require("pegreg.data_structures")
local nfst = data_structures.nfst

--- An interpreter that takes
--- the input DSL
--- list and transforms it into the
--- "nfst" data structure.
---
--- Its working type is a lua array,
--- its create type is an implementation
--- of the nfa interface.
---  @see NFA
local reify = {}

--- Implement pair by taking the first and second
--- arrays of objects and concatenating values
--- of the second table to the first table.
--- Technically breaks subtyping by requiring
--- both fst and snd to have an array rather than
--- tree structure, so be sure to use flatten first.
--- @generic T
--- @param fst T[] The first lua array of elements
--- @param snd T[] The second lua array of elements
--- @return T[] pair the two tables, concatenated
function reify.pair(fst, snd)
   for _, v in ipairs(snd) do
      table.insert(fst, v)
   end
   return fst
end

--- Reify the information relating to states.
--- @param n number The number of the state
--- @param final boolean whether the state is final
function reify.state(n, final)
   -- local out = {}
   -- out.__n = n
   -- out.__final = final
   -- function out:number()
   --    return self.__n
   -- end

   -- function out:final()
   --    return self.__final
   -- end

   -- function out:substates()
   --    return function ()
   --       return nil
   --    end
   -- end

   -- function out:contains(_)
   --    return false
   -- end
   -- return {out}
   return {
      {
         number = n,
         final = final
      }
   }
end

--- Reify the information relating to arrows.
--- @param from number
--- @param to number
--- @param input string
function reify.arrow(from, to, input, _)
   -- local out = {}
   -- out.__from = from
   -- out.__to = to
   -- out.__input = input

   -- function out:from()
   --    return self.__from
   -- end

   -- function out:to()
   --    return self.__to
   -- end

   -- function out:input()
   --    return self.__input
   -- end

   -- return {out}
   return {
      {
         from = from,
         to = to,
         input = input
      }
   }
end

--- Reify a null at the end of a list
function reify.null()
   return {}
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
         local out = lst[idx]
         idx = idx + 1
         return out
      else
         return nil
      end
   end
   return it
end

local function nub(lst)
   local out = {}
   if #lst > 0 then
      local prev = lst[1]
      table.insert(out, lst[1])
      for i = 2, #lst, 1 do
         if prev ~= lst[i] then
            table.insert(out, lst[i])
         end
         prev = lst[i]
      end
   end
   return out
end


function reify.create(states, arrows)
   -- First, nub and sort
   table.sort(states, function (a, b) return a.number < b.number end)
   table.sort(arrows, function (a, b)
                        if a.from == b.from then
                           return a.to < b.to
                        end
                        return a.from < b.from
                      end)
   states = nub(states)
   arrows = nub(arrows)

   -- Create the reified object,
   -- which will contain the information
   -- necessary to implement the NFA
   -- interface
   local reified = {}
   reified[1] = states
   reified[2] = arrows

   -- Now, make wrappers for all of the states
   local state_to_state_wrapper = {}
   local state_to_arrows = {}
   for _, state in ipairs(reified[1]) do
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

      for _, arrow in ipairs(reified[2]) do
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
   for _, arrow in ipairs(reified[2]) do
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
   for _, state in ipairs(reified[1]) do
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
      local it = make_list_it(reified[1])
      local function wrapper()
         local v = it()
         return v and state_to_state_wrapper[v.number]
      end
      return wrapper
   end

   function nfa:size()
      return #reified[1]
   end

   function nfa:arrows()
      local it = make_list_it(reified[2])
      local function wrapper()
         local v = it()
         return v and arrow_to_arrow_wrapper[v]
      end
      return wrapper
   end

   function nfa:start()
      return state_to_state_wrapper[reified[1][1].number]
   end

   return setmetatable(reified, {__index = nfa})
end

return reify
