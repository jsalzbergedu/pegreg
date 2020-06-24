--- A wrapper around lua's tables
--- using only the array part
--- and printing in lispy syntax
local list = {}

list.mt = {}

function list.assert_list(lst)
   assert(getmetatable(lst) == list.mt, tostring(lst) .. "is not a list")
end

function list.mt.__tostring(lst)
   local out = "("
   if #lst.inner > 0 then
      out = out .. tostring(lst.inner[1])
   end
   for i = 2, #lst.inner, 1 do
      out = out .. " " .. tostring(lst.inner[i])
   end
   out = out .. ")"
   return out
end

function list.mt.__len(lst)
   return lst.maxn
end

function list.mt.__ipairs(lst)
   return ipairs(lst.inner)
end

function list.mt.__pairs(lst)
   return ipairs(lst.inner)
end

function list.get(lst, pos)
   return lst.inner[pos]
end

function list.mt.__eq(lst1, lst2)
   if #lst1 < #lst2 then
      return false
   end
   for i = 1, #lst1, 1 do
      if lst1:get(i) ~= lst2:get(i) then
         return false
      end
   end
   return true
end

function list.set(lst, pos, value)
   assert(pos <= lst.maxn)
   lst.inner[pos] = value
end

function list.add(lst, item)
   lst.inner[lst.maxn + 1] = item
   lst.maxn = lst.maxn + 1
end

function list.new(...)
   local lst = {}
   lst = setmetatable(lst, list.mt)
   lst.inner = {}
   -- Avoid iterating through table
   -- just to get maxn
   lst.maxn = 0
   -- Add the indexing operations
   lst.get = list.get
   lst.set = list.set
   lst.add = list.add
   -- Everything else will be provided
   -- via wrappers to the list library
   local args = table.pack(...)
   for i = 1, args.n, 1 do
      lst:add(args[i])
   end
   return lst
end

function list.concat(lst)
   return table.concat(lst.inner)
end

function list.insert(lst, value)
   table.insert(lst.inner, value)
   lst.maxn = lst.maxn + 1
end

function list.maxn(lst)
   -- Avoid linear traversal
   -- by keeping track of the axn
   return lst.maxn
end

function list.remove(lst, pos)
   local out = table.remove(lst.inner, pos)
   lst.maxn = lst.maxn + 1
   return out
end

function list.sort(lst, comp)
   return table.sort(lst.inner, comp)
end

for k, _ in pairs(table) do
   if k ~= "unpack" and k ~= "pack" then
      assert(list[k], tostring(k) .. " not in list")
   end
end

return list
