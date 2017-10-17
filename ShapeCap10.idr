module ShapeCap10

export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

export
triangle : Double -> Double -> Shape
triangle x y = Triangle x y

export
rectangle : Double -> Double -> Shape
rectangle x y = Rectangle x y

export
circle : Double -> Shape
circle r = Circle r

public export
data ShapeView : (shape : Shape) -> Type where
  STriangle : ShapeView (triangle x y)
  SRectangle : ShapeView (rectangle x y)
  SCircle : ShapeView (circle r)

export
shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle x y) = STriangle
shapeView (Rectangle x y) = SRectangle
shapeView (Circle x) = SCircle
