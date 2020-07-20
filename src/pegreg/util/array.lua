--------------------------------------------------------------------------------
-- Utility functions for lua arrays
--------------------------------------------------------------------------------
local array = {}

--------------------------------------------------------------------------------
-- Given an array, make an iterator over it
--------------------------------------------------------------------------------
function array.make_it(arr)
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

return array
