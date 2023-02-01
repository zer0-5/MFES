# Courses

```alloy
open util/ordering[Grade]

sig Person {
	teaches : set Course,
	enrolled : set Course,
	projects : set Project
}

sig Professor, Student in Person {}

sig Course {
	projects : set Project,
	grades : Person -> Grade
}

sig Project {}

sig Grade {}
```

## Only students can be enrolled in courses

```alloy
no (Person - Student).enrolled
```

## Only professors can teach courses

```alloy
no (Person - Professor).teaches
```

## Courses must have teachers

```alloy
Course in Professor.teaches
```

## Projects are proposed by one course

```alloy
all p: Project | one Course <: projects.p
```

## Only students work on projects and projects must have someone working on them

```alloy
all p: Person | some p.projects implies p in Student
all p: Project | p in Person.projects
```

## Students only work on projects of courses they are enrolled in

```alloy
all s: Student, p: s.projects | p in s.enrolled.projects
```

## Students work on at most one project per course

```alloy
all s: Student, c: s.enrolled | lone p: s.projects | p in c.projects
```

## A professor cannot teach themselves

```alloy
all p: Professor | no p.teaches & p.enrolled
```

## A professor cannot teach colleagues

```alloy
all disj p1, p2: Professor | some p1.teaches & p2.teaches implies no (p1.teaches & p2.enrolled)
```

## Only students have grades

```alloy
all p: Person, g: Grade | p->g in Course.grades implies p in Student
```

## Students only have grades in courses they are enrolled

```alloy
all s: Student, g: Grade, c: Course | s->g in c.grades implies c in s.enrolled 
```

## Students have at most one grade per course

```alloy
all s: Student, c: Course | lone g : Grade | s->g in c.grades
```

## A student with the highest mark in a course must have worked on a project on that course

```alloy
grades.(max[Grade]) in projects.~projects
```

## A student cannot work with the same student in different projects

```alloy
all disj s1, s2: Student | lone s1.projects & s2.projects
```

## Students working on the same project in a course cannot have marks differing by more than one unit

```alloy
all p : Project, g1, g2 : (projects.p).grades[projects.p] | g1 in (g2 + prev[g2] + next[g2])
```
