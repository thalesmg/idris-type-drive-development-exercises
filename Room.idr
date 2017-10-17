module Room

import Data.Vect

data Direction = S | W | N | E

record Room where
  constructor MkRoom
  name : String
  exits : Direction -> Maybe Room

-- Inicialização
room1 : Room
room1 = MkRoom "Sala 1" (\_ => Nothing)

room2 : Room
room2 = MkRoom "Sala 2" (\dir => case dir of
                                   E => Just room1
                                   _ => Nothing)

-- Ligar sala 1 à sala 2
-- tentativa 1
room1' : Room
room1' = MkRoom "Sala 1" (\dir => case dir of
                                    W => Just room2 -- aponta para sala 2 que aponta para room1 antiga
                                    _ => Nothing)

-- tentativa 2
Rooms : Type
-- Rooms = {n : Nat} -> Vect n Room
Rooms = List Room

dungeon : Rooms
dungeon = rooms
  where
    mutual
      conn1 : Direction -> Maybe Room
      conn1 dir = case dir of
                    E => Just r2
                    _ => Nothing
      conn2 : Direction -> Maybe Room
      conn2 dir = case dir of
                    W => Just r1
                    _ => Nothing
      r1 : Room
      r1 = MkRoom "Sala 1" conn1
      r2 : Room
      r2 = MkRoom "Sala 2" conn2
      -- Quebra se define Rooms como Vect n Room !!!!
      rooms : Rooms
      rooms = [r1, r2]

-- Erro!?!
-- r1 : Room
-- r1 = index 0 dungeon

-- tentativa 3

-- simplificação: esquerda e direita
codata Room2 = MkRoom2 Room2 String Room2
