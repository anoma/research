\begin{luacode}
-- get a changing but known random seed

--[[
-- dotests = false

-- following file stuff from 

--local seed = 1655821264

--if dotests then
   seed = math.round(os.time() - os.clock() * 100000)
--else
--   seed = 1655821264
   --end
]]--

local seed = math.round(os.time() - os.clock() * 100000)
seed = tonumber(1655821263)
math.randomseed(seed)

--[[
-- Opens a file in read mode
file = io.open("./someData" .. tostring(seed) .. ".dat", "w")

-- appends a word test to the last line of the file
   file:write("--preparations start")
]]--


--fvalue holds the f of 3f+1
--maxrnd holds the value of the maximal round we want

local function setcounter(name,val)
   tex.sprint( "\\setcounter{", name, "}{", val, "}")
end

local function newcounter(name)
   tex.sprint( "\\newcounter{", name,"}")
end

local function gen_tbl(n)
   local res = {}
   for i=1,n do
      table.insert(res,tostring(i))
   end
   return res
end

local function sample(tbl, n)
   if n > #tbl then
      error("table is too short for sampling")
      return {}
   end
   if n < 0 then
      error("negative number of elements ?!")
   end
   if n == 0 then
      return {}
   end
   local theindex = math.random(1,#tbl)
   local element = tbl[theindex]
   table.remove(tbl,theindex)
   local res = sample(tbl, n-1)
   table.insert(res,element)
   return res
end

--[[
local function removeSome sample(tbl, n)
   if n > #tbl then
      error("table is too short for removing")
      return {}
   end
   if n < 0 then
      error("negative number of elements ?!")
   end
   if n == 0 then
      return tbl
   end
   local theindex = math.random(1,#tbl)
   table.remove(tbl,theindex)
   return removeSome(tbl, n-1)
end
]]--

local function contains(tbl, x)
   for _, v in ipairs(tbl) do
      if x == v then
	 return true
      end
   end
   return false
end   



local n = 3*\arabic{fvalue}+1
local q = 2*\arabic{fvalue}+1
local max = \arabic{maxrnd}

-- let's now sample the dag structure
local samples = {}
for v=1,n do
   samples[v] = {}
   for r=2,max do
      -- sample a quorum of referenced blocks
      samples[v][r] = sample( gen_tbl(n), q)
   end
end

for v,x in pairs(samples) do
   for r,l in pairs(x) do
      --tex.print(" ")
      --tex.sprint("samples of val ",tostring(v)," in round ", tostring(r),"are:")
      for i,w in ipairs(l) do
	 --tex.sprint(w, " ")
      end
      --tex.print("|")
   end
   --tex.print(".-")
end

for v=1,n do
   -- the links from blocks in round r to blocks in lower numbered rounds (r-1)
   for r=2,max do
      local blink = "linkToBlockFrom"
      blink = blink .. tostring(v) -- from validator v
      blink = blink .. "," ..  tostring(r) -- in round r
      for k=1,q do
	 local blk = blink .. "," ..  tostring(k) -- k-th link (in time)
	 newcounter(blk)
	 setcounter(blk,samples[v][r][k])
      end
   end
   -- the "support links", into the block from a successor round (r+1)
   for r=1,max-1 do
      local slink = "supportOfBlockBy"
      slink = slink .. tostring(v) -- block of validator v
      slink = slink .. "," ..  tostring(r) -- in round r
      local link_indices = 0
      for w=1,n do
	 -- if referenced, add next support link
	 if contains(samples[w][r+1],tostring(v)) then
	    link_indices = link_indices + 1
	    local slk = slink .. "," ..  tostring(link_indices)
	    -- tex.print( slk, tostring(w))
	    newcounter(slk)
	    setcounter(slk,w)
	 end
      end
      --  and a counter for how much support
      local cnt = slink .. ",count"
      newcounter(cnt)
      setcounter(cnt,link_indices)
      if link_indices == 0 then
	 --[[file:write("missing support at validator "
		    .. tostring(v)
		    .. " in round "
		    .. tostring(r))
	 ]]--	    
      end
   end
end

--[[
for 
      local blink = "linkToBlockFrom"
      blink = blink .. tostring(v) -- from validator v 
      blink = blink .. "," ..  tostring(r) -- in round r

   for l=1,q do
	 local ctr = blink .. "," .. tostring(prev[l])
	 newcounter(ctr)
      end
      if r > 1 then
	 local indeg = "inDegreeOf"
	 -- indeg = indeg .. 
      end

]]--

--[[
local x = gen_tbl(4)
tex.print("entries of x. ")
for i,v in ipairs(x) do   
   tex.sprint(v, ". ")
end

local s = sample(x,2)
tex.print("entries of s. ")
for i,v in ipairs(s) do   
   tex.sprint(v, ". ")
end
]]--


--[[
--tex.sprint("preparations done")

file:write("--preparations done")

-- closes the open file
file:close()
]]--

\end{luacode}
