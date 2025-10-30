# Restaurant Calorie Standard Verification

This restaurant chain advertises a nutritional quality standard claiming that every dish on their menu contains at least 500 calories. They market themselves as serving "substantial, satisfying meals" and say this calorie minimum applies to ALL menu items without exception.

We've got their nutrition database with calorie counts for the dishes they currently serve:
- Grilled Salmon Platter: 850 calories
- Classic Burger with Fries: 1200 calories
- Caesar Salad (full size): 520 calories
- Chicken Alfredo Pasta: 950 calories
- Steak and Potatoes: 1400 calories
- Veggie Stir Fry Bowl: 680 calories
- BBQ Ribs Combo: 1350 calories
- Shrimp Scampi: 720 calories
- Roasted Chicken Dinner: 890 calories
- Lasagna Special: 1100 calories
- Fish and Chips: 980 calories

The universal standard claim is: for any menu item X, the calorie count of X is at least 500 calories.

We can see the specific dishes and their calorie values, and they all meet the 500-calorie threshold. But does this standard actually hold for EVERY item on their menu? Not just these 11 dishes we've listed, but literally every single thing they serve including seasonal items, specials, or regional variations?

This gets interesting because we're checking a universal nutritional claim (applies to all menu items everywhere) against the finite set of dishes we have data for. The relationship between "these examples all meet the standard" and "the universal standard holds" is what creates the complexity here.

Logic: UFLIA (with quantifiers)
