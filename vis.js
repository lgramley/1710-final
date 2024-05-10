// HTML content
const htmlContent = `
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Driver-Passenger Simulation Visualizer</title>
    <style>
        /* Define styles for the grid container */
        .grid-container {
            display: grid;
            grid-template-columns: repeat(5, 50px); /* Adjust the number of columns as needed */
            grid-template-rows: repeat(3, 50px); /* Adjust the number of rows as needed */
            gap: 2px; /* Adjust the gap between cells */
            border: 2px solid #000; /* Add border for visualization */
            margin: 20px auto; /* Adjust margin as needed */
            padding: 2px;
        }
        
        /* Define styles for individual grid cells */
        .grid-cell {
            width: 100%;
            height: 100%;
            background-color: #ccc; /* Default cell color */
            border: 1px solid #000; /* Add border for visualization */
        }
    </style>
</head>
<body>
    <div class="grid-container" id="grid-container">
        <!-- Grid cells will be added dynamically here -->
    </div>

    <script>
        // Define the size of the grid
        const numRows = 3; // Adjust as needed
        const numCols = 5; // Adjust as needed

        // Get the grid container element
        const gridContainer = document.getElementById('grid-container');

        // Function to create grid cells
        function createGrid() {
            for (let row = 0; row < numRows; row++) {
                for (let col = 0; col < numCols; col++) {
                    // Create a div element for each grid cell
                    const cell = document.createElement('div');
                    cell.classList.add('grid-cell');
                    cell.dataset.row = row;
                    cell.dataset.col = col;
                    // Add the cell to the grid container
                    gridContainer.appendChild(cell);
                }
            }
        }

        // Function to add a driver to the grid at a specified location
        function addDriver(locationX, locationY) {
            const cell = document.querySelector(\`.grid-cell[data-row='\${locationY}'][data-col='\${locationX}']\`);
            if (cell) {
                cell.textContent = 'D'; // Display 'D' to represent driver
                cell.classList.add('driver');
            }
        }

        // Function to add a passenger to the grid at a specified location
        function addPassenger(locationX, locationY) {
            const cell = document.querySelector(\`.grid-cell[data-row='\${locationY}'][data-col='\${locationX}']\`);
            if (cell) {
                cell.textContent = 'P'; // Display 'P' to represent passenger
                cell.classList.add('passenger');
            }
        }

        // Example usage:
        createGrid(); // Create the grid

        // Add drivers and passengers to the grid
        addDriver(1, 1); // Example: Add a driver at location (1, 1)
        addPassenger(3, 2); // Example: Add a passenger at location (3, 2)
    </script>
</body>
</html>
`;

// Inject the HTML content into the document
document.write(htmlContent);
