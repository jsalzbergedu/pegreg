local list_fin = require("pegreg.interpreters.list_fin")
local remark_fin = require("pegreg.interpreters.remark_fin")

-- Rules that transform enumerated, finally-marked output
-- to arrows,
-- fin/notfin is abbreviated as "nfin"
-- arrows (nfin a) = (arrows a)
--
-- arrows (# N1 (empty)) = (lambda (N) {(arrow N N1 '' '')})
--
-- arrows (# N1 (lit a)) = (lambda (N) {(arrow N N1 a a)})
--
-- arrows (# N1 (seq (nfin (# N2 a)) (nfin (# N3 b)))) = (lambda (N)
--                              (arrow N N1 '' '')
--                              and append
--                              ((arrows a) N1)
--                              and append
--                              (fold append (map (arrows b) (fins a))))
--
-- arrows (# N1 (choice a b)) = (lambda (N)
--                               (arrow N N1 '' '')
--                                and append
--                                ((arrows a) N1)
--                                and append
--                                ((arrows b) N1)
--
-- arrows (# N1 (star (nfin # _ x))) = (lambda (N)
--                                      (arrow N N1 '' '')
--                                      and append
--                                      (map (lambda (N2) (arrow N2 N1 '' ''))
--                                           (fins x)))

--------------------------------------------------------------------------------
-- Create arrows is perhaps the most complicated
-- step in this process, and it is encoded in the following way.
-- Every invocation of create arrow returns a function that
-- takes an fst interpreter.
-- It also takes a function, but the entire point of this function
-- is basically just to pair its return values, a generator of
-- arrows and a construct that tracks which states are final.
--
-- This generator of arrows takes in the previous state
-- (AKA, the state from which an arrow is constructed to the
-- current state),
-- and returns a function that takes the number of the current state.
-- The function that takes the number of the current state returns
-- a list of arrows.
--
-- Every time an N is specified via mark_n,
-- the n passed into mark_n gets applied to the function that takes
-- the current number.
--
-- To extend this syntax,
-- write something along the lines of
-- return function (s, f)
--   return f(function (previous) function (current) ... end end,
--            remark_fin.something())
-- end
-- where in ..., you create and return a list of arrows.
--------------------------------------------------------------------------------
local create_arrows = {}

function create_arrows.e()
   return function (s, f)
      local function empty_arrow(previous)
         return function (current)
            return s.arrow(previous, current, '', '')
         end
      end
      return f(empty_arrow,
               remark_fin.e())
   end
end

function create_arrows.lit(lit)
   return function (s, f)
      local function lit_arrow(previous)
         return function (current)
            return s.arrow(previous, current, lit, lit)
         end
      end
      return f(lit_arrow,
               remark_fin.lit(lit))
   end
end

local function extract(arrows, finstates)
   return arrows, finstates
end

function create_arrows.seq(rule1, rule2)
   return function (s, f)
      local arrows_1, finstates_1 = rule1(s, extract)
      local arrows_2, finstates_2 = rule2(s, extract)
      local function seq_arrow(previous)
         return function (current)
            -- Go from previous to current
            local arrows_out = s.pair(s.arrow(previous, current, '', ''),
                                      s.null())
            -- Go from current to left
            arrows_out = s.pair(arrows_1(current), arrows_out)
            -- Go from fins left to right
            local fins_left = remark_fin.create(remark_fin.grammar(finstates_1))(list_fin)
            for _, v in ipairs(fins_left) do
               arrows_out = s.pair(arrows_2(v), arrows_out)
            end
            return arrows_out
         end
      end
      return f(seq_arrow, remark_fin.seq(finstates_1, finstates_2))
   end
end

function create_arrows.left(item)
   return function (s, f)
      local _, finstates = item(s, extract)
      local function left_arrow(previous)
         return function (current)
            local arrows, _ = item(s, extract)
            local out = s.pair(s.arrow(previous, current, '', ''), s.null())
            out = s.pair(arrows(current), out)
            return out
         end
      end
      return f(left_arrow,
               remark_fin.left(finstates))
   end
end

function create_arrows.right(item)
   return function (s, f)
      local _, finstates = item(s, extract)
      local function right_arrow(previous)
         return function (current)
            local arrows, _ = item(s, extract)
            local out = s.pair(s.arrow(previous, current, '', ''), s.null())
            out = s.pair(arrows(current), out)
            return out
         end
      end
      return f(right_arrow,
               remark_fin.right(finstates))
   end
end

function create_arrows.fin(item)
   return function (s, f)
      local arrows, finstates = item(s, extract)
      return f(arrows, remark_fin.fin(finstates))
   end
end

function create_arrows.notfin(item)
   return function (s, f)
      local arrows, finstates = item(s, extract)
      return f(arrows, remark_fin.notfin(finstates))
   end
end

function create_arrows.mark_n(n, item)
   return function (s, f)
      local arrows, finstates = item(s, extract)
      local function mark_n_arrow(previous)
         return arrows(previous)(n)
      end
      return f(mark_n_arrow, remark_fin.mark_n(n, finstates))
   end
end

function create_arrows.choice(rule1, rule2)
   return function (s, f)
      local arrows_1, finstates_1 = rule1(s, extract)
      local arrows_2, finstates_2 = rule2(s, extract)
      local function seq_arrow(previous)
         return function (current)
            -- Go from previous to current
            local arrows_out = s.pair(s.arrow(previous, current, '', ''),
                                      s.null())
            -- Go from current to left
            arrows_out = s.pair(arrows_1(current), arrows_out)
            -- Go from current to right
            arrows_out = s.pair(arrows_2(current), arrows_out)
            return arrows_out
         end
      end
      return f(seq_arrow, remark_fin.choice(finstates_1, finstates_2))
   end
end

function create_arrows.star(rule)
   return function (s, f)
      local arrows, finstates = rule(s, extract)
      local function star_arrow(previous)
         return function (current)
            -- Go from previous to current
            local arrows_out = s.pair(s.arrow(previous, current, '', ''),
                                      s.null())

            -- Go from current to rule
            arrows_out = s.pair(arrows(current), arrows_out)

            -- Go from fins to previous
            local fins_rule = remark_fin.create(remark_fin.grammar(finstates))(list_fin)

            -- Make fins go to current
            for _, v in ipairs(fins_rule) do
               arrows_out = s.pair(s.arrow(v, current, '', ''), arrows_out)
            end

            return arrows_out
         end
      end
      return f(star_arrow, remark_fin.star(finstates))
   end
end


function create_arrows.grammar(item)
   return function (s)
      local arrows, _ = item(s, extract)
      arrows = arrows(-1)
      return s.create(s.null(), arrows)
   end
end

function create_arrows.ref(item)
   assert(false, "Refs should be expanded")
end

function create_arrows.create(grammar)
   return grammar
end

return create_arrows
