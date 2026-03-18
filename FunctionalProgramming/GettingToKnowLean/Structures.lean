-- 1.4. Structures

#check 1.2

#check -454.2123215

#check 0.0

#check 0

#check (0 : Float)

structure Point where
  x : Float
  y : Float

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin

#eval origin.x

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

structure Point3D where
  x : Float
  y : Float
  z : Float

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

#check { x := 0.0, y := 0.0 : Point}

#check 3


-- 1.4.1. Updating Structures🔗

def zeroX' (p : Point) : Point :=
  { x := 0, y := p.y }


def zeroX (p : Point) : Point :=
  { p with x := 0 }

def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }

#eval zeroX fourAndThree

#eval fourAndThree


-- 1.4.2. Behind the Scenes🔗

#check Point.mk 1.5 2.8

#check {x := 1.5, y :=  2.8 : Point}

#check Point.mk

structure Point' where
  point ::
  x : Float
  y : Float

#check Point'.point

#eval "one string".append " and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

 #eval fourAndThree.modifyBoth Float.floor


-- 1.4.3. Exercises🔗

-- Define a structure named RectangularPrism that contains the height, width, and depth of a rectangular prism, each as a Float.

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

-- Define a function named volume : RectangularPrism → Float that computes the volume of a rectangular prism.

def volume (rp : RectangularPrism) : Float :=
  rp.height * rp.width * rp.depth

#check volume

-- Define a structure named Segment that represents a line segment by its endpoints, and define a
-- function length : Segment → Float that computes the length of a line segment. Segment should have at most two fields.

structure Segment where
  startPoint : Point
  endPoint : Point

def length (segment : Segment) : Float :=
  distance segment.startPoint segment.endPoint

-- Which names are introduced by the declaration of RectangularPrism?

-- Which names are introduced by the following declarations of Hamster and Book? What are their types?

-- structure Hamster where
--   name : String
--   fluffy : Bool

-- structure Book where
--   makeBook ::
--   title : String
--   author : String
--   price : Float
