-- Bedlam Cube in Haskell
-- Copyright 2005-2023 Simon Guest
-- Licensed under GNU General Public License v3

module Main where

import qualified List as L

type Coord = [Int]

class Coordinated a where
   coords :: a -> [Coord]

--
-- rotational transformations in 3 space
--
type Transform = [[Int]]

-- return permutations of a list
permutations :: [a] -> [[a]]
permutations [] = []
permutations [x] = [[x]]
permutations (x:xs) = L.concatMap (insertions x) (permutations xs)
insertions x [] = [[x]]
insertions x (y:ys) = (x:y:ys) : (map (y:) (insertions x ys))

-- return a number of choices
choices :: Num a => a -> [b] -> [[b]]
choices 0 xs = []
choices 1 xs = map (\x -> [x]) xs
choices n xs = L.concatMap (\ys -> map (\x -> x:ys) xs) (choices (n-1) xs)

-- includes reflections, need to filter just those with det 3 to get rotations
transforms = let mul c t = map (c *) t in
   L.concatMap (\t -> map (\c -> zipWith mul c t)
                          (choices 3 [1,-1]))
               (permutations [[1,0,0],[0,1,0],[0,0,1]])
rot_transforms :: [Transform]
rot_transforms = filter (\x -> (det x == 3)) transforms

-- determinant of a matrix
-- 2 x 2
det [[a,b],[c,d]] = a * d - b * c
-- n x n
det rows = sum $ zipWith (*)
                         (zipWith (*) alts (concat rows))
                         (map det (m rows))
 where
   alts = iterate (* (-1)) 1
   m rows = let n = length rows - 1 in
      zipWith (\ (x,y) rs -> map (!!- y) (rs !!- x))
              [(i,j) | i <- [0..n], j <- [0..n]]
              (repeat rows)
   (!!-) xs n = take n xs ++ drop (n+1) xs

dotProduct :: Num a => [a] -> [a] -> a
dotProduct xs ys = sum $ zipWith (*) xs ys

transform_coord :: Transform -> Coord -> Coord
transform_coord t c = map (dotProduct c) t

transform_coords t cs = map (transform_coord t) cs

class Transformable a where
   transform :: Transform -> a -> a

rotations :: (Eq a, Transformable a) => a -> [a]
rotations x = map (\t -> transform t x) rot_transforms

--
-- bounded offsets
--

type Boundary = ([Int], [Int])          -- lower left bottom, upper right top

class Boundable a where
   bounds :: a -> Boundary

data Offset = Offset [Int]

offset_coord :: Offset -> [Int] -> [Int]
offset_coord (Offset o) c = zipWith (+) o c

class Offsettable a where
   offset :: Offset -> a -> a

bounded_offsets :: (Offsettable a, Boundable a) => Boundary -> a -> [a]
bounded_offsets (p0,q0) x =
   let (p,q) = bounds x
       [px,py,pz] = zipWith (-) p0 p
       [qx,qy,qz] = zipWith (-) q0 q
       offsets = [Offset [x,y,z] | x <- [px..qx], y <- [py..qy], z <- [pz..qz]]
   in
      map (\o -> offset o x) offsets

--
-- types for cube
--

-- pieces

data Cell = Cell [Int]
   deriving (Eq, Ord, Show)
instance Transformable Cell where
   transform t (Cell c) = Cell (transform_coord t c)
instance Offsettable Cell where
   offset o (Cell c) = Cell (offset_coord o c)

data LCell = LCell Label Cell
   deriving (Eq, Show)
instance Ord LCell where
   compare (LCell _ c1) (LCell _ c2) = compare c1 c2
instance Transformable LCell where
   transform t (LCell lbl c) = LCell lbl (transform t c)
instance Offsettable LCell where
   offset o (LCell lbl c) = LCell lbl (offset o c)
instance Boundable LCell where
   bounds (LCell _ (Cell c)) = (c,c)
same_cell (LCell _ c1) (LCell _ c2) = c1 == c2
label (LCell lbl _) = lbl

data Piece = Piece [LCell]
   deriving (Eq, Show)
instance Coordinated Piece where
   coords (Piece lcells) = map (\ (LCell _ (Cell c)) -> c) lcells
instance Transformable Piece where
   transform t (Piece lcells) = Piece (map (transform t) lcells)
instance Offsettable Piece where
   offset o (Piece lcells) = Piece (map (offset o) lcells)
instance Boundable Piece where
   bounds p = bdy (c,c) cs
    where
      (c:cs) = coords p
      bdy (c1,c2) [] = (c1,c2)
      bdy ([ax,ay,az], [bx,by,bz]) (([cx,cy,cz]):cs)
         = bdy ([min ax cx, min ay cy, min az cz],
                [max bx cx, max by cy, max bz cz]) cs

piece :: Label -> [Coord] -> Piece
piece lbl cs = Piece [LCell lbl (Cell c) | c <- cs]


-- merge sorted lists
merge [] ys = ys
merge xs [] = xs
merge (x:xs) (y:ys) = if x < y then x : merge xs (y:ys)
                               else y : merge (x:xs) ys

-- are sorted lists distinct? (i.e. zero intersection)
distinct [] ys = True
distinct xs [] = True
distinct (x:xs) (y:ys) = if same_cell x y then False
                         else if x < y then distinct xs (y:ys)
                         else distinct (x:xs) ys

-- cycle a list
cycle' :: [a] -> [a]
cycle' (x:xs) = xs ++ [x]

-- return all possible cycles
cycles :: [a] -> [[a]]
cycles xs = take (length xs) $ iterate cycle' xs

remove_duplicates xs = reverse $ dedupe [] xs
   where dedupe ys [] = ys
         dedupe ys (x:xs) = if x `elem` ys then dedupe ys xs
                            else dedupe (x:ys) xs

-- Generate all rotations of all pieces, except for first.
-- By not rotating first piece, we exclude rotationally equivalent
-- solutions.
orientations = [head pieces] : map (\x -> rotations x) (tail pieces)

-- Generate bounded offsets of all pieces
placements = map (\xs -> concatMap (\x -> bounded_offsets box x) xs)
                 orientations

-- Now replace each piece with a sorted list of its cells, and remove
-- duplicates
canonical_placements =
   map (remove_duplicates . map (\ (Piece lcells) -> L.sort lcells))
       placements

-- extract list of pieces from labelled cells
extract :: [LCell] -> [Piece]
extract lcells = let
   lcs = L.sort $ map (\ (LCell lbl (Cell c)) -> (lbl,c)) lcells
   ext [] = []
   ext (x:xs) = let
      lbl = fst x
      ys = takeWhile (\y -> fst y == lbl) xs
      zs = dropWhile (\y -> fst y == lbl) xs
      cs = map snd (x:ys)
    in
      (piece lbl cs) : (ext zs)
 in
   ext lcs

--
-- Puzzle
--

solution = map extract $ fit_pieces [[]] canonical_placements

-- Find first empty cell
first_unused used = find all_cells used where
   all_cells = L.sort $ bounded_offsets box (LCell NoLabel (Cell [0,0,0]))
   find (c:_) [] = c
   find (c:cs) (u:us) = if same_cell c u then find cs us else c


fit_piece' used p = let
   -- only select orientations which fill the first empty cell
   first = first_unused used
   p' = filter (\x -> same_cell (head x) first) p
   -- now try to fit the piece
   p'' = filter (distinct used) p'
 in
   map (\x -> merge x used) p''

fit_piece useds p = concatMap (\used -> fit_piece' used p) useds

fit_pieces useds [] = useds
fit_pieces useds pieces =
   -- consider each piece in turn
   concatMap (\ (p:ps) -> fit_pieces (fit_piece useds p) ps)
             (cycles pieces)

--
-- pieces
--

data Label = NoLabel 
           | T | B1 | B2 | B3 | B4 | Y1 | Y2 | Y3 | Y4 | R1 | R2 | R3 | R4
   deriving (Eq, Ord, Show)


t   = piece T [[0,1,0],
               [0,1,1],
               [1,0,0],
               [1,1,0]]
b1  = piece B1 [[0,2,0],
                [1,0,0],
                [1,1,0],
                [1,2,0],
                [2,1,0]]
b2  = piece B2 [[0,0,0],
                [0,1,0],
                [0,2,0],
                [1,1,0],
                [1,1,1]]
b3  = piece B3 [[0,0,0],
                [0,1,0],
                [0,2,0],
                [0,2,1],
                [1,1,0]]
b4  = piece B4 [[0,1,0],
                [0,2,0],
                [1,1,0],
                [1,1,1],
                [1,0,1]]
y1  = piece Y1 [[0,1,0],
                [0,2,0],
                [1,0,0],
                [1,1,0],
                [2,0,0]]
y2  = piece Y2 [[0,0,0],
                [0,1,0],
                [0,2,0],
                [1,2,0],
                [1,2,1]]
y3  = piece Y3 [[0,0,0],
                [0,1,0],
                [0,2,0],
                [0,2,1],
                [1,0,0]]
y4  = piece Y4 [[0,0,0],
                [0,1,0],
                [0,2,0],
                [0,1,1],
                [1,1,0]]
r1  = piece R1 [[0,1,0],
                [1,0,0],
                [1,1,0],
                [1,2,0],
                [2,1,0]]
r2  = piece R2 [[0,0,0],
                [0,1,0],
                [0,2,0],
                [0,0,1],
                [1,0,0]]
r3  = piece R3 [[0,1,0],
                [0,2,0],
                [1,0,0],
                [1,1,0],
                [1,0,1]]
r4  = piece R4 [[0,1,0],
                [0,2,0],
                [0,1,1],
                [1,0,0],
                [1,1,0]]

pieces = [t,b1,b2,b3,b4,y1,y2,y3,y4,r1,r2,r3,r4]

box = ([0,0,0],[3,3,3])

main = do
   let sols = zip [1..] solution
   sequence_ (map (\ (i,s) -> ( (putStrLn $ "=== solution " ++ show i)
                              >> (putStrLn $ show s)
                              >> (putStrLn "")
                              )
                  ) sols)
   putStrLn $ (show $ length sols) ++ " solutions"
