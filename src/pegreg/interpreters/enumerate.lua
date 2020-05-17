local mark_fin = require("pegreg.interpreters.mark_fin")

----------------------------------------------------------------------------
-- An interpreter that performs a depth first search
-- and numbers all the nodes.
-- Adds the method "mark_n"
---------------------------------------------------------------------------
local enumerate = {}


local function extract(item, sum)
   return item, sum
end

function enumerate.fin(item)
   return function (i, n, k)
      local child, sum_child = item(i, n, extract)
      return k(i.fin(child), sum_child)
   end
end

function enumerate.notfin(item)
   return function (i, n, k)
      local child, sum_child = item(i, n, extract)
      return k(i.notfin(child), sum_child)
   end
end

function enumerate.e()
   return function (i, n, k)
      return k(i.mark_n(n + 1, i.e()), n + 1)
   end
end


function enumerate.lit(lit)
   return function (i, n, k)
      return k(i.mark_n(n + 1, i.lit(lit)), n + 1)
   end
end

function enumerate.seq(rule1, rule2)
   return function (i, n, k)
      local mark_self = n + 1
      local left, sum_left = rule1(i, n + 1, extract)
      local right, sum_right = rule2(i, sum_left, extract)
      return k(i.mark_n(mark_self, i.seq(left, right)), sum_right)
   end
end

function enumerate.choice(rule1, rule2)
   return function (i, n, k)
      local mark_self = n + 1
      local left, sum_left = rule1(i, n + 1, extract)
      local right, sum_right = rule2(i, sum_left, extract)
      return k(i.mark_n(mark_self, i.choice(left, right)), sum_right)
   end
end

function enumerate.star(item)
   return function (i, n, k)
      local mark_self = n + 1
      local child, sum_child = item(i, n + 1, extract)
      return k(i.mark_n(mark_self, i.star(child)), sum_child)
   end
end

function enumerate.right(item)
   return function (i, n, k)
      local mark_self = n + 1
      local child, sum_child = item(i, n + 1, extract)
      return k(i.mark_n(mark_self, i.right(child)), sum_child)
   end
end

function enumerate.left(item)
   return function (i, n, k)
      local mark_self = n + 1
      local child, sum_child = item(i, n + 1, extract)
      return k(i.mark_n(mark_self, i.left(child)), sum_child)
   end
end

function enumerate.ref(rule, rules)
   assert(false, "Refs ought to be expanded")
end

function enumerate.grammar(item)
   return function (i)
      local item, _ = item(i, -1, extract)
      return i.grammar(item)
   end
end

function enumerate.create(grammar)
   return function (i)
      return i.create(grammar(i))
   end
end

local function extract(item, sum)
   return item, sum
end

function enumerate.fin(item)
   return function (i, n, k)
      local child, sum_child = item(i, n, extract)
      return k(i.fin(child), sum_child)
   end
end

function enumerate.notfin(item)
   return function (i, n, k)
      local child, sum_child = item(i, n, extract)
      return k(i.notfin(child), sum_child)
   end
end

function enumerate.e()
   return function (i, n, k)
      return k(i.mark_n(n + 1, i.e()), n + 1)
   end
end


function enumerate.lit(lit)
   return function (i, n, k)
      return k(i.mark_n(n + 1, i.lit(lit)), n + 1)
   end
end

function enumerate.seq(rule1, rule2)
   return function (i, n, k)
      local mark_self = n + 1
      local left, sum_left = rule1(i, n + 1, extract)
      local right, sum_right = rule2(i, sum_left, extract)
      return k(i.mark_n(mark_self, i.seq(left, right)), sum_right)
   end
end

function enumerate.choice(rule1, rule2)
   return function (i, n, k)
      local mark_self = n + 1
      local left, sum_left = rule1(i, n + 1, extract)
      local right, sum_right = rule2(i, sum_left, extract)
      return k(i.mark_n(mark_self, i.choice(left, right)), sum_right)
   end
end

function enumerate.star(item)
   return function (i, n, k)
      local mark_self = n + 1
      local child, sum_child = item(i, n + 1, extract)
      return k(i.mark_n(mark_self, i.star(child)), sum_child)
   end
end

function enumerate.right(item)
   return function (i, n, k)
      local mark_self = n + 1
      local child, sum_child = item(i, n + 1, extract)
      return k(i.mark_n(mark_self, i.right(child)), sum_child)
   end
end

function enumerate.left(item)
   return function (i, n, k)
      local mark_self = n + 1
      local child, sum_child = item(i, n + 1, extract)
      return k(i.mark_n(mark_self, i.left(child)), sum_child)
   end
end

function enumerate.ref(rule, rules)
   assert(false, "Refs ought to be expanded")
end

function enumerate.grammar(item)
   return function (i)
      local item, _ = item(i, -1, extract)
      return i.grammar(item)
   end
end

function enumerate.create(grammar)
   return function (i)
      return i.create(grammar(i))
   end
end

return enumerate
