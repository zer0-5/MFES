# Instagram

```alloy
sig User {
    follows : set User,
    sees : set Photo,
    posts : set Photo,
    suggested : set User
}

sig Influencer extends User {}

sig Photo {
    date : one Day
}
sig Ad extends Photo {}

sig Day {}
```

## Every image is posted be one user

```alloy
all p: Photo | one posts.p
```

## An user cannot follow itself

```alloy
all u: User | u not in u.follows
```

## An user only sees (non ad) photos posted by followed users. Ads can be seen by everyone

```alloy
all u: User | u.sees in u.follows.posts + Ad
```

## If an user posts an ad then all its posts should be labelled as ads

```alloy
all u: User | (some p : u.posts | p in Ad) implies u.posts in Ad
```

## Influencers are followed by everyone else

```alloy
all i: Influencer | all u: User - i | i in u.follows
```

## Influencers post every day

```alloy
all d: Day, i: Influencer | d in i.posts.date
```

## Suggested are other users followed by followed users, but not yet followed

```alloy
all u: User | u.suggested = u.follows.follows - u.follows - u
```

## An user only sees ads from followed or suggested users

```alloy
all u: User | all p: u.sees | p in Ad implies p in (u.follows + u.suggested).posts
```
