module ShapeTestCap10

import ShapeCap10

area : Shape -> Double
area x with (shapeView x)
  area (triangle y z) | STriangle = y * z / 2
  area (rectangle y z) | SRectangle = y * z
  area (circle r) | SCircle = pi * r * r
