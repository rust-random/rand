import numpy as np
import matplotlib.pyplot as plt


OUT = "target"
EXT = "png"


def standard_normal():
    from scipy.stats import norm
    # Possible values for the distribution
    x = np.linspace(-3, 3, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for the standard normal distribution
    ax.plot(x, norm.pdf(x), label='Standard normal')

    # Adding title and labels
    ax.set_title('Standard normal distribution')
    ax.set_xlabel('Z-score (standard deviations from the mean)')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/standard_normal.{EXT}")
    plt.close()


def chi_squared():
    def y(x, df):
        from scipy.stats import chi2
        y = chi2.pdf(x, df)
        y[y > 1.0] = np.nan
        return y
    # Degrees of freedom for the distribution
    df_values = [1, 2, 3, 5, 9]
    # Possible values for the distribution
    x = np.linspace(0, 10, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for each value of the degrees of freedom
    for df in df_values:
        ax.plot(x, y(x, df), label=f'df = {df}')

    # Adding title and labels
    ax.set_title('Chi-squared distribution')
    ax.set_xlabel('Chi-squared statistic')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/chi_squared.{EXT}")
    plt.close()


def bernoulli():
    # Defining the Bernoulli distribution PMF
    def y(p):
        return np.array([1 - p, p])

    # Possible values of p for the distribution
    p_values = [0.1, 0.5, 0.9]
    # Possible outcomes for a Bernoulli distributed variable
    outcomes = np.array([0, 1])

    # Creating the figure and the axis
    fig, ax = plt.subplots()
    # Width of each bar
    width = 0.2

    # Plotting the PMF for each value of p
    for i, p in enumerate(p_values):
        ax.bar(outcomes - width / 2 + i * width - 0.1, y(p), width=width, label=f'p = {p}')

    # Adding title and labels
    ax.set_title('Bernoulli distribution')
    ax.set_xlabel('Outcome')
    ax.set_ylabel('Probability')
    ax.set_xticks(outcomes)  # set the ticks to be the outcome values

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/bernoulli.{EXT}")
    plt.close()


def binomial():
    # Defining the Binomial distribution PMF
    def y(n, p, k):
        from scipy.stats import binom
        return binom.pmf(k, n, p)

    n = 10
    p = 0.2
    # Possible outcomes for a Binomial distributed variable
    outcomes = np.arange(0, 11)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PMF for each value of n and p
    ax.bar(outcomes, y(n, p, outcomes), label=f'n = {n}, p = {p}')

    # Adding title and labels
    ax.set_title('Binomial distribution')
    ax.set_xlabel('k (number of successes)')
    ax.set_ylabel('Probability')
    ax.set_xticks(outcomes)  # set the ticks to be the outcome values

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/binomial.{EXT}")
    plt.close()


def cauchy():
    # Possible values for the distribution
    x = np.linspace(-7, 7, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    inputs = [(0, 0.5), (0, 1), (0, 2), (-2, 1)]

    # Plotting the PDF for the Cauchy distribution
    for x0, gamma in inputs:
        ax.plot(x, 1 / (np.pi * gamma * (1 + ((x - x0) / gamma)**2)), label=f'x₀ = {x0}, γ = {gamma}')

    # Adding title and labels
    ax.set_title('Cauchy distribution')
    ax.set_xlabel('x')
    ax.set_ylabel('P(x)')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/cauchy.{EXT}")
    plt.close()


def dirichlet():
    def plot_dirichlet(alpha, ax):
        """
        Plots a Dirichlet distribution given alpha parameters and axis.
        """
        # Create a 2D meshgrid of points
        resolution = 200  # Resolution of the visualization
        x = np.linspace(0, 1, resolution)
        y = np.linspace(0, 1, resolution)
        X, Y = np.meshgrid(x, y)
        # Flatten the grid to pass to the distribution
        XY = np.vstack((X.flatten(), Y.flatten()))

        # Calculate remaining coordinate for the 3-simplex (3D Dirichlet is defined on a triangle in 2D)
        Z = 1 - X - Y
        # Filter out points outside the triangle
        valid = (Z >= 0)
        # Prepare the probability density function (PDF) array
        PDF = np.zeros(X.shape).flatten()

        # Calculate PDF only for valid points
        if np.any(valid):
            from scipy.stats import dirichlet
            # The 3rd coordinate for the Dirichlet distribution
            Z_valid = Z.flatten()[valid]
            # Stack the coordinates for the distribution input
            XYZ_valid = np.vstack((XY[:, valid], Z_valid))
            # Calculate the Dirichlet PDF
            PDF[valid] = dirichlet.pdf(XYZ_valid.T, alpha)

        # Reshape PDF back into the 2D shape of the grid
        PDF = PDF.reshape(X.shape)

        # Create a contour plot on the provided axis
        contour = ax.contourf(X, Y, PDF, levels=15, cmap='Blues')
        # Add a colorbar
        plt.colorbar(contour, ax=ax, pad=0.05, aspect=10)
        # Set limits and labels
        ax.set_xlim(0, 1)
        ax.set_ylim(0, 1)
        ax.set_xticks([])
        ax.set_yticks([])
        ax.set_xlabel(r'$x_1$', fontsize=12)
        ax.set_ylabel(r'$x_2$', fontsize=12)
        # Set title for the subplot
        ax.set_title(r'$\alpha = {}$'.format(alpha), fontsize=14)

    # Define alpha parameters for the Dirichlet distributions to be plotted
    alpha_params = [
        (1.5, 1.5, 1.5),
        (5.0, 5.0, 5.0),
        (1.0, 2.0, 2.0),
        (2.0, 4.0, 8.0)
    ]

    # Create a figure with subplots
    fig, axes = plt.subplots(2, 2, figsize=(10, 8))

    # Loop through the list of alpha parameters
    for alpha, ax in zip(alpha_params, axes.flatten()):
        plot_dirichlet(alpha, ax)

    plt.savefig(f"{OUT}/dirichlet.{EXT}")
    plt.close()


def exponential():
    # Defining the Exponential distribution PDF
    def y(lmbda, x):
        from scipy.stats import expon
        return expon.pdf(x, scale=1 / lmbda)

    # Possible values of lambda for the distribution
    lambda_values = [0.5, 1, 2]
    # Possible values for the distribution
    x = np.linspace(0, 5, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for each value of lambda
    for lmbda in lambda_values:
        ax.plot(x, y(lmbda, x), label=f'λ = {lmbda}')

    # Adding title and labels
    ax.set_title('Exponential distribution')
    ax.set_xlabel('x')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/exponential.{EXT}")
    plt.close()


def gamma():
    # Defining the Gamma distribution PDF
    def y(alpha, beta, x):
        from scipy.stats import gamma
        return gamma.pdf(x, alpha, scale=1 / beta)

    # Possible values of alpha for the distribution
    alpha_values = [1, 2, 3]
    # Possible values of beta for the distribution
    beta_values = [0.5, 1, 2]
    # Possible values for the distribution
    x = np.linspace(0, 10, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for each value of alpha and beta
    for alpha in alpha_values:
        for beta in beta_values:
            ax.plot(x, y(alpha, beta, x), label=f'α = {alpha}, β = {beta}')

    # Adding title and labels
    ax.set_title('Gamma distribution')
    ax.set_xlabel('x')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/gamma.{EXT}")
    plt.close()


def poisson():
    # Defining the Poisson distribution PMF
    def y(lmbda, k):
        from scipy.stats import poisson
        return poisson.pmf(k, lmbda)

    # Possible values of lambda for the distribution
    lambda_values = [0.5, 1, 2, 4, 10]
    # Possible outcomes for a Poisson distributed variable
    outcomes = np.arange(0, 15)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PMF for each value of lambda
    for i, lmbda in enumerate(lambda_values):
        ax.plot(outcomes, y(lmbda, outcomes), 'o-', label=f'λ = {lmbda}')

    # Adding title and labels
    ax.set_title('Poisson distribution')
    ax.set_xlabel('Outcome')
    ax.set_ylabel('Probability')
    ax.set_xticks(outcomes)  # set the ticks to be the outcome values

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/poisson.{EXT}")
    plt.close()


def weibull():
    # Defining the Weibull distribution PDF
    def y(alpha, x):
        from scipy.stats import weibull_min
        return weibull_min.pdf(x, alpha)

    # Possible values of alpha for the distribution
    alpha_values = [0.5, 1, 2]
    # Possible values for the distribution
    x = np.linspace(0, 5, 1000)

    # Creating the figure and the axis
    fig, ax = plt.subplots()

    # Plotting the PDF for each value of alpha
    for alpha in alpha_values:
        ax.plot(x, y(alpha, x), label=f'α = {alpha}')

    # Adding title and labels
    ax.set_title('Weibull distribution')
    ax.set_xlabel('x')
    ax.set_ylabel('Probability density')

    # Adding a legend
    ax.legend()

    plt.savefig(f"{OUT}/weibull.{EXT}")
    plt.close()


if __name__ == "__main__":
    # standard_normal()
    # bernoulli()
    # chi_squared()
    # binomial()
    # cauchy()
    # dirichlet()
    exponential()
    gamma()
    poisson()
    weibull()
