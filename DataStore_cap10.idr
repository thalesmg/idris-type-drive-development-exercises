module DataStoreCap10

import Data.Vect

infixr 5 .+.

public export
data Schema = SString | SInt | (.+.) Schema Schema

public export
SchemaType : Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

export
record DataStore (schema : Schema) where
  constructor MkData
  size : Nat
  items : Vect size (SchemaType schema)

export
empty : DataStore schema
empty = MkData 0 []

export
addToStore : (value : SchemaType schema) -> (store : DataStore schema) -> DataStore schema
addToStore value (MkData _ items) = MkData _ (value :: items)

public export
data StoreView : DataStore schema -> Type where
  SNil : StoreView empty
  SAdd : (rec : StoreView store) -> StoreView (addToStore value store)

storeViewHelp : (items : Vect size (SchemaType schema)) ->
                StoreView (MkData size items)
storeViewHelp [] = SNil
storeViewHelp (x :: xs) = SAdd (storeViewHelp xs)

export
storeView : (store : DataStore schema) -> StoreView store
storeView (MkData size items) = storeViewHelp items

testStore : DataStore (SString .+. SInt)
testStore = addToStore ("First", 1) $
            addToStore ("Second", 2) $
            empty

getValues : DataStore (SString .+. val_schema) -> List (SchemaType val_schema)
getValues store with (storeView store)
  getValues store | SNil = []
  getValues (addToStore (label, value) store) | (SAdd rec) =
    value :: getValues store | rec
