--------------------------------------------------------------------------------
-- An interpreter that returns a list of final states
--------------------------------------------------------------------------------
local list_fin = {}

function list_fin.e()
   return function (f)
      return f({}, false)
   end
end

function list_fin.lit(lit)
   return function (f)
      return f({}, false)
   end
end

local function extract(lst, t)
   return lst, t
end

function list_fin.seq(rule1, rule2)
   return function (f)
      local lst1, _ = rule1(extract)
      local lst2, _ = rule2(extract)
      local out = {}
      for _, v in ipairs(lst1) do
         table.insert(out, v)
      end
      for _, v in ipairs(lst2) do
         table.insert(out, v)
      end
      return f(out, false)
   end
end

function list_fin.choice(rule1, rule2)
   return list_fin.seq(rule1, rule2)
end

function list_fin.grammar(item)
   local lst, _ = item(extract)
   return lst
end

function list_fin.ref(rule, rules)
   assert(false, "Refs should be expanded")
end

function list_fin.create(grammar)
   return grammar
end

function list_fin.star(item)
   return item
end

function list_fin.left(item)
   return item
end

function list_fin.right(item)
   return item
end

function list_fin.fin(item)
   local lst, _ = item(extract)
   return function (f)
      return f(lst, true)
   end
end

function list_fin.notfin(item)
   local lst, _ = item(extract)
   return function (f)
      return f(lst, false)
   end
end

function list_fin.mark_n(n, item)
   return function (f)
      local lst, t = item(extract)
      local out = {}
      for _, v in ipairs(lst) do
         table.insert(out, v)
      end
      if t then
         table.insert(out, n)
      end
      return f(out, false)
   end
end

return list_fin
