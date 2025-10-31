# tla-broadcast-model
Project part of the DARE 2025 where a broadcast model was written using TLA+ and PlusCal. 

## Getting Started

### Prerequisites
- Download and install the [TLA+ Toolbox](https://lamport.azurewebsites.net/tla/toolbox.html)

### Importing the Specification

1. Launch the TLA+ Toolbox
2. Go to `File > Open Spec > Add New Spec...`
3. Browse to select the `all_broadcast.tla` file from this repository
4. Click "Finish" to create the specification

### Running the Model

1. In the Toolbox, open the specification
2. Go to `TLC Model Checker > (New) or Open Model > select model`
4. If created new model check that variables and parameters are set correctly
3. Click the "Model Check" button (green play button) to verify the specification

## File Structure

- `all_broadcast.tla` - Main specification file
- `all_broadcast.toolbox/` - Contains model checking configurations and results

For more details about TLA+ and the Toolbox, visit [TLA+ Home Page](https://lamport.azurewebsites.net/tla/tla.html)
