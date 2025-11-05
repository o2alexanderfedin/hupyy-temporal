# Three-Day Music Festival Scheduling

We're putting together this music festival that runs Friday through Sunday. It's not like Coachella or anything, more like a regional festival, but still pretty big.

There are 100 bands total that need to perform over the three days. We've got 5 stages set up around the festival grounds - Main Stage, Rock Stage, Electronic Tent, Acoustic Stage, and the Late Night Stage.

Each band gets a set time that's either 45 minutes or 60 minutes depending on how popular they are. Headliners get the full hour, smaller acts get 45 minutes. The festival runs from noon to midnight each day, so that's 12 hours per day times 3 days.

The Main Stage is the biggest and needs at least 30 minutes between acts for changeover - you know, clearing the stage, sound check for the next band, all that. The other stages are smaller and only need 15 minutes between acts.

We need to make sure that certain bands don't overlap because fans will want to see both. Like if you've got two popular indie bands, you probably don't want them playing at the same time on different stages. People will be bummed if they have to choose.

Also some bands have riders about when they'll play - some only do evening sets, some prefer afternoon, stuff like that. And the headliners obviously go on last each night on the Main Stage.

There's also this thing where bands that are touring together should play the same day if possible, and there are a few bands that have beef with each other so they should be on different days entirely.

Oh and sound bleed is an issue - the Main Stage and Rock Stage are kind of close to each other, so if they're both going at the same time, the sound mixes weird. They can overlap a little bit, but ideally we want like a 30 minute offset between their sets.

Can we schedule all 100 bands across 5 stages over 3 days without conflicts and keeping everyone happy?

Scale: 100 bands, 5 stages, 3 days, 36 hours total runtime, ~100 set times
Logic: QF_IDL + QF_LIA
