module Cap12_Votes

record Votes where
  constructor MkVotes
  upvotes : Integer
  downvotes : Integer

record Article where
  constructor MkArticle
  title : String
  url : String
  score : Votes

initPage : (title : String) -> (url : String) -> Article
initPage title url = MkArticle title url (MkVotes 0 0)

getScore : Article -> Integer
getScore (MkArticle _ _ (MkVotes up down)) = up - down

badSite : Article
badSite = MkArticle "Bad Page" "aaaaaaaa" (MkVotes 5 47)

goodSite : Article
goodSite = MkArticle "Goood Page" "aaaaaaaa" (MkVotes 101 7)

addUpvote : Article -> Article
addUpvote = record { score->upvotes $= (+1) }

addDownvote : Article -> Article
addDownvote = record { score->downvotes $= (+1) }
